-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_lemma_D_11
-- name    : TradingPostNSW.Leontief.Supplement.lemma_D_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:41:09.541812+00:00
-- url     : https://prove2.me/theorems/5de4a8c5-c445-48e5-aa72-9a5d1bd13847
-- title:
--   Lemma D.11, p. 29 (used in the proof of Theorem D.12) — the expected payoff is strictly concave when some likely profile bids on every good
-- statement:
--   Let agent $i$ have a utility $U_i:[0,1]^m\to\mathbb R$ that is concave, non-decreasing, non-negative and non-satiated. Let $\sigma_{-i}$ be mixed strategies of the other agents, each an arbitrary Borel probability measure concentrated on its strategy set, and suppose some profile $s'_{-i}$ played with positive probability bids on every good: $\sum_{k\ne i}s'_{k,j}>0$ for all $j$. Then agent $i$'s expected payoff in the Trading Post game without fee,
--   $$u_i^{\sigma_{-i}}(s_i)=\int U_i\big(x_i(s_i,s_{-i})\big)\,d(\bigotimes_{k\ne i}\sigma_k)(s_{-i}),$$
--   is strictly concave on $S_i$.
--
--   Differences from the source:
--   - encoding: s′_{−i} played with positive probability → every opponent assigns positive measure to the singleton containing its component of s′; reason: independence and finitely many opponents make the probability of the joint singleton positive exactly when every marginal singleton has positive measure
--   - encoding: mixed strategies are probability distributions over S_i (p. 25); equations (20)–(23) write expectations as sums → arbitrary Borel probability measures, admissible almost surely, with product-measure expectations; purity means Dirac marginals; reason: includes discrete and atomless strategies; integrability in IsMixedNE requires the displayed expectations to be actual expectations, not Lean totality values
--   - generalization: u_i : ℝ^m_+ → ℝ concave, non-negative, non-decreasing and non-satiated (Appendix D.3) → these conditions only on the box [0,1]^m; reason: every Trading Post allocation lies in the box, so payoffs use only these values; a utility satisfying the conditions on ℝ^m_+ satisfies them on the box, and §2 defines utilities on [0,1]^m
--   - encoding: non-satiated: u(x) > u(y) if x_j ≥ y_j for all j and x_j > y_j for some j → strictly monotone on the box [0,1]^m in the product order; reason: the same condition, stated on the domain of the utilities
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
--   - generalization: the ambient market assumptions m > 0, B_k ≥ 1, and enough competition from §2 and Appendix D.3 → these analytic lemmas impose only the displayed utility assumptions and admissibility of opponents; no market-wide competition or budget lower bound is assumed; reason: the concavity conclusions depend on nonnegative opponent bids and the stated positive-sum conditions, not on utility functions of other players or a budget normalization; every source market remains an instance
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 29, Lemma D.11 and its proof; (23), p. 28

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open MeasureTheory

namespace TradingPostNSW.Leontief.Supplement

theorem lemma_D_11 {n m : ℕ} (I : Instance n m) (U : Fin n → (Fin m → ℝ) → ℝ)
    (i : Fin n) (hU : IsConcaveUtility (U i)) (hns : StrictMonoOn (U i) (box m))
    (σ : Fin n → ProbabilityMeasure (Fin m → ℝ))
    (hσ : ∀ k, k ≠ i → ∀ᵐ b ∂(σ k : Measure (Fin m → ℝ)), Strategy I k b)
    (hval : ∃ s' : Fin n → Fin m → ℝ, (∀ k, k ≠ i → 0 < (σ k : Measure (Fin m → ℝ)) {s' k}) ∧
      ∀ j, 0 < ∑ k ∈ Finset.univ.erase i, s' k j) :
    StrictConcaveOn ℝ {b : Fin m → ℝ | Strategy I i b}
      (fun b => expPay U 0 (Function.update σ i (pureBid b)) i) := by sorry

end TradingPostNSW.Leontief.Supplement
