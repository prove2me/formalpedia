-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_jof_polyDeriv_sum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:27.832843+00:00
-- url     : https://prove2.me/theorems/49db0780-4f92-4e2b-9fc5-ef099196d29d
-- title:
--   I2: jof poly Deriv sum
-- statement:
--   The I2 construction uses the jof poly Deriv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L141-L144

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

theorem ReciprocityTheory.ChartRestriction.G.I2.jof_polyDeriv_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ)
    (x : W) : polyDeriv (∑ i ∈ s, P i) u F x = ∑ i ∈ s, polyDeriv (P i) u F x := by sorry
