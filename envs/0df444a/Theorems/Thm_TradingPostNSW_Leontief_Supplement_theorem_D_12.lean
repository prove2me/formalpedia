-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_theorem_D_12
-- name    : TradingPostNSW.Leontief.Supplement.theorem_D_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:41:41.996878+00:00
-- url     : https://prove2.me/theorems/82f2152e-29ec-47a8-ab2b-a8929fe2e1c7
-- title:
--   Theorem D.12, p. 29 — with concave utilities and enough competition every Nash equilibrium of Trading Post is pure
-- statement:
--   Let every agent have a utility $U_i:[0,1]^m\to\mathbb R$ that is concave, non-decreasing, non-negative and non-satiated, budgets $B_i\ge1$, and assume **enough competition**: for every good $j$ there are two distinct agents whose marginal utility for $j$ is infinite at zero, i.e. $(U(x+te_j)-U(x))/t\to+\infty$ as $t\downarrow0$ at every bundle $x$ with $x_j=0$. Then every mixed Nash equilibrium of the Trading Post game without fee is pure.
--
--   Differences from the source:
--   - reading: ∂u_i/∂x_{ij}(x) is infinity at bundles x with x_j = 0 → the right difference quotient in direction e_j tends to +∞ at every bundle of the box with x_j = 0; reason: utilities are only concave, not differentiable; the one-sided derivative of a concave function exists in [−∞, +∞] and this is the case +∞
--   - encoding: mixed strategies are probability distributions over S_i (p. 25); equations (20)–(23) write expectations as sums → arbitrary Borel probability measures, admissible almost surely, with product-measure expectations; purity means Dirac marginals; reason: includes discrete and atomless strategies; integrability in IsMixedNE requires the displayed expectations to be actual expectations, not Lean totality values
--   - generalization: u_i : ℝ^m_+ → ℝ concave, non-negative, non-decreasing and non-satiated, with enough competition at bundles of ℝ^m_+ (Appendix D.3) → these conditions only on the box [0,1]^m; reason: every Trading Post allocation lies in the box, so payoffs use only these values; a utility satisfying the conditions on ℝ^m_+ satisfies them on the box, and §2 defines utilities on [0,1]^m
--   - encoding: non-satiated: u(x) > u(y) if x_j ≥ y_j for all j and x_j > y_j for some j → strictly monotone on the box [0,1]^m in the product order; reason: the same condition, stated on the domain of the utilities
--   - encoding: the Trading Post allocation x_{i,j} = b_{i,j}/Σ_k b_{k,j} if b_{i,j} > 0, else 0 (p. 12) → the base allocation of TP(0), whose effective bids equal the bids for every b ≥ 0; reason: the same allocation on every strategy profile
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 29, Theorem D.12; proof pp. 29–30; Appendix D.3, p. 28

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open MeasureTheory

namespace TradingPostNSW.Leontief.Supplement

theorem theorem_D_12 {n m : ℕ} (I : Instance n m) (hI : GenStanding I)
    (U : Fin n → (Fin m → ℝ) → ℝ) (hU : ∀ i, IsConcaveUtility (U i))
    (hns : ∀ i, StrictMonoOn (U i) (box m)) (hec : EnoughCompetition U)
    (σ : Fin n → ProbabilityMeasure (Fin m → ℝ)) (hσ : IsMixedNE I U 0 σ) :
    IsPure σ := by sorry

end TradingPostNSW.Leontief.Supplement
