-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_half_not_integral
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.half_not_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:35.745628+00:00
-- url     : https://prove2.me/theorems/f13ce676-0ec9-4115-b927-6c6caefc7739
-- title:
--   Semi Pt: half not integral
-- statement:
--   The Semi Pt construction uses the half not integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZ.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegZ.lean#L10-L24

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegW
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.half_not_integral {K : Type} [Field K] [NumberField K] : ¬ IsIntegralElt ((2 : K)⁻¹) := by sorry
