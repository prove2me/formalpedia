-- Prove2me | Theorems.Thm_QTDecode_Parallel_theorem_12
-- name    : QTDecode.Parallel.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:17.466953+00:00
-- url     : https://prove2.me/theorems/13d624af-9626-4b5c-885a-3c9e547b6eb6
-- title:
--   Theorem 12, p. 20 (= Theorem 2, p. 6) — few active vertices ⇒ some local codeword lowers |Z| by (1 − ε)|x_v|
-- statement:
--   Fix $\varepsilon\in(0,1)$ and $\delta,\kappa>0$. There is $\Delta_0$ such that the following holds for every $\Delta\ge\Delta_0$. Let $G$ be a finite group with $A=A^{-1}$, $B=B^{-1}$, $|A|=|B|=\Delta$, such that $\mathrm{Cay}(G,A)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs; let $C_A,C_B$ have minimum distance at least $\delta\Delta$ and let $C_A\otimes\mathbb F_2^B+\mathbb F_2^A\otimes C_B$ be $\kappa$-product-expanding. Let $Z\ne0$ be a mismatch vector with a minimum decomposition $Z=C_0+R_0+C_1+R_1$ whose sets of active vertices $S_{ij}\subseteq V_{ij}$ satisfy, for all $i,j\in\{0,1\}$,
--   $$|S_{ij}|\ \le\ \frac1{2^{12}}\,\delta^2\varepsilon^3\kappa\,|V_{00}|.$$
--   Then there exist a vertex $v$ and a non-zero codeword $x_v$ of the dual tensor code on $Q(v)$ such that
--   $$|Z|-|Z+x_v|\ \ge\ (1-\varepsilon)\,|x_v|.$$
--
--   This is the core technical result of the decoder analysis: as long as a minimum decomposition of the mismatch has few active vertices, the sequential decoder can always make progress.
--
--   **Formalization Note** Three conventions are made explicit. (1) "$\Delta$ large enough", used in the proof (p. 24, "for large enough $\Delta$, we have a contradiction"), is $\exists\Delta_0$ depending on $\varepsilon,\delta,\kappa$ only. (2) The conclusion asks for a non-zero $x_v$: with $x_v=0$ it holds trivially, and the proof contradicts the decoder being stalled, which concerns non-zero codewords (p. 17). (3) Accordingly $Z\ne0$ is assumed; for $Z=0$ no non-zero $x_v$ can lower the weight. $|V_{00}|=|G|$.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 20, Theorem 12 (= Theorem 2, p. 6; proof pp. 20–24)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Theorem 12, p. 20 (= Theorem 2, p. 6), with "`Δ` large enough" (used in its proof, p. 24) made
explicit and `Z ≠ 0`, `x_v ≠ 0` added (with `x_v = 0` the conclusion is empty). Fix `ε ∈ (0, 1)`,
`δ, κ > 0`. There is `Δ₀` such that for `Δ ≥ Δ₀`, non-bipartite Ramanujan `Cay(G, A)`, `Cay(G, B)`,
local codes `C_A`, `C_B` of minimum distance at least `δΔ` with `κ`-product-expanding dual tensor
code: if the active sets of a minimum decomposition of a non-zero mismatch `Z` satisfy
`|S_ij| ≤ 2⁻¹² δ²ε³κ|V₀₀|` for all `i, j`, then some vertex `v` and some non-zero dual tensor codeword
`x_v` on `Q(v)` satisfy `|Z| − |Z + x_v| ≥ (1 − ε)|x_v|`. -/
theorem theorem_12 :
    ∀ ε δ κ : ℝ, 0 < ε → ε < 1 → 0 < δ → 0 < κ →
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (A B : Finset G),
      A.card = Δ → B.card = Δ →
      (∀ a ∈ A, a⁻¹ ∈ A) → (∀ b ∈ B, b⁻¹ ∈ B) →
      IsRamanujanAdj (leftCayleyAdj A) Δ →
      (∀ k, ascEigenvalues (leftCayleyAdj A) k ≠ -(Δ : ℝ)) →
      IsRamanujanAdj (rightCayleyAdj B) Δ →
      (∀ k, ascEigenvalues (rightCayleyAdj B) k ≠ -(Δ : ℝ)) →
      ∀ (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2)),
      HasMinDistAtLeast CA (δ * Δ) → HasMinDistAtLeast CB (δ * Δ) →
      IsProductExpanding CA CB Δ κ →
      ∀ (Z : G × A × B → ZMod 2) (D : Decomp (G × A × B)),
      IsMinDecomp CA CB Z D → Z ≠ 0 →
      (∀ i j : Bool, ((activeSet D i j).card : ℝ) ≤
        1 / 2 ^ 12 * δ ^ 2 * ε ^ 3 * κ * (Fintype.card G : ℝ)) →
      ∃ (v : G × (Bool × Bool)) (x : A × B → ZMod 2), x ∈ dualTensorCode CA CB ∧ x ≠ 0 ∧
        (1 - ε) * (hammingNorm x : ℝ) ≤
          (hammingNorm Z : ℝ) - (hammingNorm (Z + qtPush v x) : ℝ) := by sorry

end QTDecode.Parallel
