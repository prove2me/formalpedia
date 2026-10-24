-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_smoothMax_domination
-- name    : QAlgorithms.Papers.Independent.Support50.P21.smoothMax_domination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:49:14.394442+00:00
-- url     : https://prove2.me/theorems/cb137500-cf83-4ab9-8e32-bc82ace297ff
-- title:
--   Lemma 14
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho,\sigma$ be density operators, $\Delta\ge0$, and $\lambda\in\mathbb R$ with $\rho\le2^\lambda\sigma+\Delta$. For every $\varepsilon\ge\sqrt{8\operatorname{Tr}\Delta}$,
--
--   $$D_{\max}^{\varepsilon}(\rho\Vert\sigma)\le\lambda.$$
--
--   Smoothing uses $B^\varepsilon(\rho)=\{\bar\rho\ge0:\lVert\bar\rho-\rho\rVert_1\le\varepsilon,\ \operatorname{Tr}\bar\rho\le\operatorname{Tr}\rho\}$. Approximants may be subnormalized and $\varepsilon$ may exceed one. This converts approximate domination to a smooth max-divergence bound.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 7, Lemma 14

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- Lemma 14, PDF p.7; construction pp.10–11: subnormalized approximants,
full trace norm, exponent lambda, and eps allowed to exceed one. -/
theorem smoothMax_domination (rho sigma Delta : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hDelta : Delta.PosSemidef) (lambda eps : ℝ)
    (hdom : Le rho ((((2 : ℝ) ^ lambda) : ℂ) • sigma + Delta))
    (heps : Real.sqrt (8 * tr Delta) ≤ eps) :
    traceSmoothMax eps rho sigma ≤ (lambda : EReal) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
