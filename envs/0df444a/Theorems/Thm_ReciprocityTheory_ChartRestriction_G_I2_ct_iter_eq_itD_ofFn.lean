-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_eq_itD_ofFn
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_iter_eq_itD_ofFn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:00.680595+00:00
-- url     : https://prove2.me/theorems/c50f60b7-2559-5b93-9a45-f23aac40ad61
-- title:
--   I2: ct iter eq it D of Fn
-- statement:
--   The I2 construction uses the ct iter eq it D of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L189-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L189-L198

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

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_iter_eq_itD_ofFn {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (F : W → ℂ) (x : W)
    (j : ℕ) (w : Fin j → W) : iteratedFDeriv ℂ j F x w = itD F (List.ofFn w) x := by sorry
