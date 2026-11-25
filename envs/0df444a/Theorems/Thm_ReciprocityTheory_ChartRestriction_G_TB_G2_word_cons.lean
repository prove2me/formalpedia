-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_word_cons
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.word_cons
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:25.126971+00:00
-- url     : https://prove2.me/theorems/2362c57e-2fa5-474f-9d67-eb5529753603
-- title:
--   G2: word cons
-- statement:
--   The G2 construction uses the word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EvalZeroReplicateAppend.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EvalZeroReplicateAppend.lean#L19-L21

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CcTMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type}

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.word_cons (l : ι) (Ls : List ι) (m : ι →₀ ℕ) :
    word (l :: Ls) m = List.replicate (m l) l ++ word Ls m := by sorry
