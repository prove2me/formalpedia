-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_monomial_one
-- name    : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_monomial_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:30.148827+00:00
-- url     : https://prove2.me/theorems/8f756c16-eed8-44f3-9577-5392bf049c2d
-- title:
--   I2: poly Deriv monomial one
-- statement:
--   The I2 construction uses the poly Deriv monomial one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PolyDerivMonomialOne.lean#L154-L158

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

theorem ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_monomial_one (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x = pdTerm u F x m := by sorry
