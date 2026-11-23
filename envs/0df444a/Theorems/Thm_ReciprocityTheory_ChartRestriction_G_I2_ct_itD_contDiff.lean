-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_contDiff
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_itD_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:47.202521+00:00
-- url     : https://prove2.me/theorems/0501ea04-66a8-436b-8a6e-1c2f22f3d5db
-- title:
--   I2: ct it D cont Diff
-- statement:
--   The I2 construction uses the ct it D cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L140-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L140-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_itD_contDiff {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (l : List W) :
    ContDiff ℂ (⊤ : ℕ∞) (fun y => itD f l y) := by sorry
