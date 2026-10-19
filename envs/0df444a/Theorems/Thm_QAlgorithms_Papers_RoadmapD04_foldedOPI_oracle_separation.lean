-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapD04_foldedOPI_oracle_separation
-- name    : QAlgorithms.Papers.RoadmapD04.foldedOPI_oracle_separation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:46:14.359985+00:00
-- url     : https://prove2.me/theorems/8268a3f2-dfaa-4bdb-aa0b-4e859d4e6f43
-- title:
--   Folded OPI: uniform DQI advantage and sampled-oracle classical query lower bound
-- statement:
--   Fix a rational rate $R\in(0,1)$. An admissible block count $M>0$ satisfies $M+1=2^u$ for an integer $u>0$, and $K=\lfloor RN\rfloor\ge h$, where $h=M+2$, $N=hM$ and $q=N+1=(M+1)^2$. Work over the publicly represented characteristic-two field $\mathbb F_q$, with a fixed public primitive element $\gamma$. Put $J=\lfloor K/h\rfloor$ and $\Sigma=\mathbb F_q^h$. A promised instance consists of arbitrary sets $A_i\subseteq\Sigma$ with $|A_i|=|\Sigma|/2$, accessed only through separately callable fixed-block XOR membership oracles. Each call chooses its block classically and may query a superposition of whole symbols.
--
--   A coefficient vector $x\in\mathbb F_q^K$ represents the polynomial $Q_x(Y)=\sum_{j=0}^{K-1}x_jY^j$, including the zero polynomial. Its score is
--   $$
--   \operatorname{score}_{\mathcal A}(Q_x)=\frac1M\sum_{i=0}^{M-1}
--   \mathbf1\!\left[(Q_x(\gamma^{ih+j}))_{j=0}^{h-1}\in A_i\right].
--   $$
--   Define
--   $$
--   \alpha_C(R)=\frac{1+R}{2},\qquad
--   \alpha_Q(R)=\frac{1+\sqrt{R(2-R)}}2.
--   $$
--
--   1. There is a uniform quantum polynomial-time DQI family using one query to each fixed-block oracle, at most $M$ queries in total. Its expected score converges to $\alpha_Q(R)$ uniformly over every promised instance:
--   $$
--   \forall\epsilon>0\ \exists M_0\ \forall\text{ admissible }M\ge M_0\
--   \forall\mathcal A,\quad
--   \left|\mathbb E[\operatorname{score}_{\mathcal A}(Q_{\rm DQI})]-\alpha_Q(R)\right|\le\epsilon.
--   $$
--   The construction uses the conventional unfolded scalar GRS dual syndrome decoder at cutoff $\ell=\lfloor(J-1)/2\rfloor$, strictly below half its scalar minimum distance, the explicit top-window layer weights, and synthesis accuracy $M^{-2}$. Its polynomial resource bounds and classical circuit constructor are independent of the acceptance sets.
--
--   2. A randomized polynomial-time implementation of Prange's information-set algorithm makes at most $4M$ membership queries in the worst case. It samples uniformly with replacement until obtaining accepted targets in the first $J$ blocks, interpolates their $hJ$ evaluations, and returns zero if the total trial cap is exhausted. When the sets $A_i$ are sampled independently and uniformly among half-size subsets, independently of the algorithm's randomness,
--   $$
--   \forall\epsilon,\delta>0\ \exists M_0\ \forall\text{ admissible }M\ge M_0,\quad
--   \Pr\!\left[\left|\operatorname{score}(Q_{\rm Prange})-\alpha_C(R)\right|>\epsilon\right]\le\delta.
--   $$
--
--   3. For each fixed $0<\eta<1-\alpha_C(R)$, there are $\theta,c>0$ and $M_0\ge2$, depending only on $R,\eta$, such that every admissible $M\ge M_0$ and every randomized classical algorithm with worst-case query budget $T\le\exp(\theta M/\log M)$ satisfy
--   $$
--   \Pr[\operatorname{score}(A(\omega))\ge\alpha_C(R)+\eta]\le e^{-cM}.
--   $$
--   The probability is over the same sampled acceptance sets and independent algorithm randomness. Computation between queries and arbitrary finite advice are unrestricted, provided the description and advice are fixed before sampling.
--
--   This result separates the approximation scores attainable through the same whole-symbol membership interface. The quantum assertion is an expectation guarantee for every promised oracle; the classical assertions are distributional.
--
--   **Formalization Note** A fixed effective polynomial-basis binary field representation and uniform compilation over $\{H,T,\mathrm{CNOT}\}$ make the implicit public representation and polynomial runtime concrete. The DQI state, its coefficient output wires and its query count are tied to one circuit. The sampled probabilities are finite uniform averages of normalized classical output laws.
-- source:
--   A provable quantum advantage for approximate optimization via decoded quantum interferometry, arXiv:2610.02145v2, Theorem 1 (continues on PDF p.16), PDF p. 15. https://arxiv.org/abs/2610.02145v2 . PDF SHA-256: 4b140366a174c1f0ea1883aa1de514e5ff8e0fda8be240f4214cb2b6a27ea7bf.

import Definitions.Def_QAlgorithms_Defs_FoldedPrange
import Definitions.Def_QAlgorithms_Papers_RoadmapD04_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapD04

open FoldedOPI FoldedDQI










/-- Theorem 1 (all three clauses), arXiv:2610.02145v2, PDF/printed pp.15–16.
R is the fixed rational limiting rate. PublicDomain supplies every admissibility condition.
The existential families supply effective public representation, uniform polynomial runtime,
fixed-block XOR access, conventional unfolded GRS decoding and capped Prange.
The DQI expectation converges uniformly for each promised oracle. Classical probabilities
average independent uniform half-size sets and independent algorithm randomness.
Lower-bound constants precede sizes, budgets, algorithms and arbitrary finite advice. -/
theorem foldedOPI_oracle_separation (R : ℚ) (hR : 0 < R ∧ R < 1) :
    ∃ (C : PrangeRealization R) (F : UniformFixedBlockFamily R)
      (width : ∀ P, (C.fieldData P).encoding.e * Nat.clog 2 (C.fieldData P).encoding.p = 2 * P.u),
      (∀ P : PublicDomain, P.rate = R → IsSourceDQI F C P (width P)) ∧
      (∀ eps : ℝ, 0 < eps → ∃ M0 : ℕ, ∀ P : PublicDomain,
        P.rate = R → M0 ≤ P.M → ∀ A : BalancedInstance P.M (Symbol P),
          |quantumScoreMean F P (C.fieldData P) (width P) A -
            (1 + Real.sqrt ((R : ℝ) * (2 - (R : ℝ)))) / 2| ≤ eps) ∧
      (∀ eps delta : ℝ, 0 < eps → 0 < delta → ∃ M0 : ℕ, ∀ P : PublicDomain,
        P.rate = R → M0 ≤ P.M →
          sampledPrangeProbability P (C.fieldData P) (C.distinct P) (C.dimensions P)
            (fun s => eps < |s - (1 + (R : ℝ)) / 2|) ≤ delta) ∧
      (∀ eta : ℝ, 0 < eta → eta < 1 - (1 + (R : ℝ)) / 2 →
        ∃ theta c : ℝ, 0 < theta ∧ 0 < c ∧ ∃ M0 : ℕ, 2 ≤ M0 ∧
          ∀ P : PublicDomain, P.rate = R → M0 ≤ P.M →
          ∀ T : ℕ, (T : ℝ) ≤ Real.exp (theta * P.M / Real.log P.M) →
          ∀ A : RandDecisionTree (Fin P.M × Symbol P) Bool
            (Fin (publicParameters P 3) → publicField P),
          RandMakesAtMost A T →
            sampledClassicalProbability P (C.fieldData P) A
              (fun s => (1 + (R : ℝ)) / 2 + eta ≤ s) ≤ Real.exp (-c * P.M)) := by sorry

end QAlgorithms.Papers.RoadmapD04
