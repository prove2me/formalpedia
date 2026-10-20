-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_F_convex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.F_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:50:36.334423+00:00
-- url     : https://prove2.me/theorems/00495efb-68c1-438e-9cd9-7359e7b9df22
-- title:
--   Convexity in the Renyi order
-- statement:
--   Fix positive semidefinite ρ and σ with nested supports. With Fα defined by (17) and log 0=−∞, the function of the order α is convex on [1,∞). Equivalently its real epigraph is convex:
--
--   $$
--   \{(\alpha,t)\in[1,\infty)\times\mathbb R:F_\alpha(\rho\Vert\sigma)\leq t\}\text{ is convex}.
--   $$
--
--   This convexity controls the order dependence and the Legendre transforms used in hypothesis testing.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 7, Corollary III.11 (convexity)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.7: Convexity in the Renyi order. The real epigraph also handles rho=0, when F is identically −infinity, without undefined products of zero and infinity. -/
theorem F_convex (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (hsupp : SupportLE rho sigma) :
    Convex ℝ {p : ℝ × ℝ | 1 ≤ p.1 ∧ F p.1 rho sigma ≤ (p.2 : EReal)} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
