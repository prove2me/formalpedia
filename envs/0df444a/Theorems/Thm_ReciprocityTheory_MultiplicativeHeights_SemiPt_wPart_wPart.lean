-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_wPart_wPart
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.wPart_wPart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:10.634773+00:00
-- url     : https://prove2.me/theorems/8f21b4b9-7aea-5036-beab-0e44f49b79e0
-- title:
--   Semi Pt: w Part w Part
-- statement:
--   The Semi Pt construction uses the w Part w Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean#L16-L21

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
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

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.wPart_wPart (r m : ℕ) (i : Fin r) : wPart r m (wPart r m i) = i := by sorry
