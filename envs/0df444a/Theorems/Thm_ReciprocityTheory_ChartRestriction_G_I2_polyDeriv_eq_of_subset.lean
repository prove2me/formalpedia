-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_eq_of_subset
-- name    : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_eq_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:24.545424+00:00
-- url     : https://prove2.me/theorems/7569e2cc-7a61-4cdf-8d62-5bb0b570b242
-- title:
--   I2: poly Deriv eq of subset
-- statement:
--   The I2 construction uses the poly Deriv eq of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L122-L129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_eq_of_subset (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W)
    {S : Finset (σ →₀ ℕ)} (hS : P.support ⊆ S) :
    polyDeriv P u F x = ∑ m ∈ S, P.coeff m * pdTerm u F x m := by sorry
