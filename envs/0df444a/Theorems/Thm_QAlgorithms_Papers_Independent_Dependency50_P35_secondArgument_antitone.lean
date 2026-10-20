-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_secondArgument_antitone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.secondArgument_antitone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:53:06.369643+00:00
-- url     : https://prove2.me/theorems/591d7a85-cd31-4a69-95c4-8a65b6bc2b67
-- title:
--   Proposition 4: antitonicity in the second operator
-- statement:
--   Let $\rho\ge0$ be nonzero and $\sigma'\ge\sigma\ge0$ in the Loewner order. For $\alpha\in[1/2,1)\cup(1,\infty)$,
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma')\le\widetilde D_\alpha(\rho\|\sigma).
--   $$
--
--   Here the divergence is trace-normalized, base two, and extended-real valued. Increasing the reference operator cannot increase divergence; no normalization or domination hypothesis is imposed.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 8, Proposition 4

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.8, Proposition 4: no support domination or trace normalization imposed. -/
theorem secondArgument_antitone {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a ∧ a ≠ 1) (rho sigma sigma2 : Mat I)
    (hr : rho.PosSemidef) (hn : rho ≠ 0) (hs : sigma.PosSemidef)
    (horder : (sigma2 - sigma).PosSemidef) :
    divergence a rho sigma2 ≤ divergence a rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
