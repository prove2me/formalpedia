-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapE06_singleShot_sequential
-- name    : QAlgorithms.Papers.RoadmapE06.singleShot_sequential
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:35:48.309369+00:00
-- url     : https://prove2.me/theorems/07f88c10-ddcc-4a3f-b869-8c3028735f0f
-- title:
--   Single-shot Tanner decoding: sequential decoder residual-weight guarantee
-- statement:
--   Fix code parameters $\rho,d_r,\kappa\in(0,1)$ and decoder parameters $0<2\delta<\varepsilon<1$. For all sufficiently large degrees $\Delta$ (with the threshold depending only on these fixed parameters), let $G$ be a finite group with symmetric generating sets $A,B$ of size $\Delta$, whose left and right Cayley graphs are Ramanujan in the paper's sense: their second largest adjacency eigenvalue is at most $2\sqrt{\Delta-1}$. Let the binary local codes $C_A,C_B$ have exact rates $\rho,1-\rho$, respectively. Each of $C_A,C_B,C_A^\perp,C_B^\perp$ has distance at least $d_r\Delta$, and both dual tensor codes $C_A\boxplus C_B$ and $C_A^\perp\boxplus C_B^\perp$ are $\kappa$-product-expanding.
--
--   Construct the quadripartite quantum Tanner code on $Q=G\times A\times B$, with $n=|G|\Delta^2$ qubits, X checks from $C_A\otimes C_B$ at $V_{00}\cup V_{11}$ and Z checks from $C_A^\perp\otimes C_B^\perp$ at $V_{01}\cup V_{10}$. Let $d$ be its actual CSS distance. Let $e\in\mathbb F_2^Q$ be an X error and $D$ a binary error on the vertex-labelled Z checks. Write $|e|_R=\min_{s\in C_X^\perp}|e+s|$ and let $|D|_V$ count vertices with at least one nonzero syndrome-error bit. Define
--
--   $$
--   A_\varepsilon=\frac{24}{\kappa\Delta(1-\varepsilon)},\quad B_\varepsilon=\frac{3\Delta}{\kappa(1-\varepsilon)},\quad C_\delta=\frac{d_r^2\delta^3\kappa}{2^{12}\Delta^2},\quad c_1=\frac{\varepsilon-2\delta}{\varepsilon(1-\delta)},\quad c_2=\frac2\varepsilon.
--   $$
--
--   If
--
--   $$
--   A_\varepsilon|e|_R+B_\varepsilon|D|_V\le\min(C_\delta n,d/\Delta),
--   $$
--
--   then Algorithm 1, receiving only $\widetilde\sigma=H_Ze+D$ and parameter $\varepsilon$, terminates and every lawful output $\widehat f$ satisfies
--
--   $$
--   |e+\widehat f|_R\le\left(1+\frac{2c_2}{\kappa c_1}\right)\Delta^2|D|_V.
--   $$
--
--   Local minimum-weight choices are fixed consistently before the input; infeasible local syndromes use the zero fallback. Algorithm 2 starts with zero accumulators, uses the stated weight-decrease test and minimum column/row decomposition, and halts only at zero mismatch or when no permitted move exists. Algorithm 1 returns $\sum_{v\in V_{01}}\widetilde\varepsilon_v+\widehat C_1+\widehat R_0$.
--
--   This is the quantitative adversarial single-shot guarantee for the sequential Tanner decoder. With $D=0$, the residual is a stabilizer, rather than necessarily the zero vector.
--
--   **Formalization Note** The printed theorem leaves decoder domains implicit; the range above is inherited from pp.14 and 22. The distance is an extended natural minimum; when both logical-error sets are empty it is infinite, and the threshold uses only $C_\delta n$. Termination is represented by existence of a terminal execution together with the bound for every lawful terminal execution. No stochastic residual support law is asserted.
-- source:
--   Single-shot decoding of good quantum LDPC codes, arXiv:2306.12470v2, Theorem 4.17 (Main Theorem for the Sequential Decoder), PDF p. 26. https://arxiv.org/abs/2306.12470v2 . PDF SHA-256: 5f0fcbd29c8ba3214af7293007e0fb046a73d290abfc3e0e49ae7c8c8dad11af.

import Definitions.Def_QAlgorithms_Defs_NoisyTannerDecoding
import Definitions.Def_QAlgorithms_Papers_RoadmapE06_Model
set_option autoImplicit false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapE06

open QAlgorithms.NoisyTanner


/-- Theorem 4.17 (Main Theorem for the Sequential Decoder), arXiv:2306.12470v2,
PDF pp.26–27; Algorithms 1–2 on p.13; standing construction assumptions on pp.4–7.
The inherited parameter domain is made explicit: `0 < delta`, `2 * delta < eps < 1`
(p.22). This clarifies the printed theorem's unspecified domains without changing
its bound or its non-strict threshold. The degree threshold depends only on the
fixed code/decoder parameters and precedes the group, code, check presentation,
selector and errors. `CodeData` carries the symmetric generating sets, exact
rates, four local-distance bounds, two product-expansion conditions and the
source's one-sided second-eigenvalue Ramanujan convention. The decoder is fixed
before the errors and receives only the noisy syndrome. A terminal execution
exists, and every lawful terminal execution satisfies the printed residual bound.
The frozen `sequentialDecoder` uses the source's `V_01`, `C_hat_1 + R_hat_0`
output, a consistent minimum-weight local selector with zero fallback, and
maximal termination. No decomposability or residual bound is assumed. -/
theorem singleShot_sequential
    (rate relativeDistance kappa delta eps : ℝ)
    (hrate : 0 < rate ∧ rate < 1)
    (hdistance : 0 < relativeDistance ∧ relativeDistance < 1)
    (hkappa : 0 < kappa ∧ kappa < 1)
    (hdelta : 0 < delta) (hseparation : 2 * delta < eps) (heps : eps < 1) :
    ∃ degreeThreshold : ℕ, 1 ≤ degreeThreshold ∧
      ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G],
      ∀ C : CodeData G, C.rate = rate → C.relativeDistance = relativeDistance →
        C.kappa = kappa → degreeThreshold ≤ C.degree →
      ∀ (H : CheckPresentation C) (selector : LocalCorrectionSelector H),
      let parameters : ConstantDomain :=
        { degree := C.degree
          degree_pos := C.degree_pos
          kappa := kappa
          relativeDistance := relativeDistance
          delta := delta
          eps := eps
          kappa_pos := hkappa.1
          relativeDistance_range := hdistance
          delta_pos := hdelta
          separation := hseparation
          eps_lt := heps }
      let constants := decoderConstants parameters
      let finiteThreshold := constants 2 * (Fintype.card G * C.degree ^ 2 : ℕ)
      let threshold := if tannerQuantumDistance C = ⊤ then finiteThreshold
        else min finiteThreshold (((tannerQuantumDistance C).toNat : ℝ) / (C.degree : ℝ))
      ∀ (e : G × C.A × C.B → ZMod 2)
        (D : {v : G × (Bool × Bool) // v.2.1 ≠ v.2.2} × Fin H.zCount → ZMod 2),
        constants 0 * (reducedWeight C e : ℝ) +
          constants 1 * (syndromeVertexWeight H D : ℝ) ≤ threshold →
        (∃ correction, sequentialDecoder selector eps (noisySyndrome H e D) correction) ∧
        ∀ correction, sequentialDecoder selector eps (noisySyndrome H e D) correction →
          (reducedWeight C (e + correction) : ℝ) ≤
            constants 5 * (syndromeVertexWeight H D : ℝ) := by sorry

end QAlgorithms.Papers.RoadmapE06
