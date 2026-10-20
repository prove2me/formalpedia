-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_auxiliary_variational
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.auxiliary_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:08:18.234495+00:00
-- url     : https://prove2.me/theorems/8d1c58d3-da8d-4dd4-83b7-ae7366d157d3
-- title:
--   Equation (11): auxiliary variational representation
-- statement:
--   Let $\rho\ge0$ have trace one, let $\sigma\ge0$, and let $\alpha\in(0,1)\cup(1,\infty)$. Using exactly the auxiliary quantity of Definition 5, including its composed-support guards and extended scalar logarithm,
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma)=\sup_{\tau\ge0,\ \operatorname{Tr}\tau\le1}\widetilde D_\alpha(\rho\|\sigma;\tau).
--   $$
--
--   If $\rho\sigma\ne0$ and either $\sigma\gg\rho$ or $\alpha<1$, this also equals
--
--   $$
--   \frac{\alpha}{\alpha-1}\log_2\left\|\rho^{1/2}\sigma^{(1-\alpha)/\alpha}\rho^{1/2}\right\|_\alpha.
--   $$
--
--   Otherwise the divergence is $+\infty$. These guards preserve Definition 2's singular cases instead of allowing the generalized inverse to erase them.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 15, Equation (11)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.15, (11): unrestricted auxiliary supremum; the norm expression is
restricted to the finite domain of Definition 2, with +infinity otherwise. -/
theorem auxiliary_variational {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a ∧ a ≠ 1) (rho sigma : Mat I) (hr : Density rho)
    (hs : sigma.PosSemidef) :
    divergence a rho sigma =
      sSup {v : EReal | ∃ tau : Mat I, tau.PosSemidef ∧ tr tau ≤ 1 ∧
        v = auxiliaryRenyi a rho sigma tau} ∧
    (rho * sigma ≠ 0 ∧ (Dominates sigma rho ∨ a < 1) →
      divergence a rho sigma = ((a/(a-1) : ℝ) : EReal) *
        elog (schatten a (spectralPower rho (1/2 : ℝ) * spectralPower sigma ((1-a)/a) * spectralPower rho (1/2 : ℝ)))) ∧
    (¬ (rho * sigma ≠ 0 ∧ (Dominates sigma rho ∨ a < 1)) →
      divergence a rho sigma = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
