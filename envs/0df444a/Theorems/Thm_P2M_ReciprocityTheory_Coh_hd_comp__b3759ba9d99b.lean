-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_comp__b3759ba9d99b
-- name    : P2M_ReciprocityTheory_Coh_hd_comp__b3759ba9d99b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:09.236732+00:00
-- url     : https://prove2.me/theorems/c25886b2-3fd6-5a7b-ab12-372a37dcc4c4
-- title:
--   P2 M Reciprocity Theory Coh hd comp  b3759ba9d99b: P2 M Reciprocity Theory Coh hd comp  b3759ba9d99b
-- statement:
--   The P2 M Reciprocity Theory Coh hd comp  b3759ba9d99b construction uses the P2 M Reciprocity Theory Coh hd comp  b3759ba9d99b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L51-L52

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
variable {V X Y : Type u} [AddCommGroup V]

theorem P2M_ReciprocityTheory_Coh_hd_comp__b3759ba9d99b (n : ℕ) (F : (Fin (n + 1) → Y) → V) (c : X → Y) (x : Fin (n + 2) → X) :
    hd n (fun y => F fun i => c (y i)) x = hd n F (fun i => c (x i)) := by sorry

alias «ReciprocityTheory».«Coh».«hd_comp'» := P2M_ReciprocityTheory_Coh_hd_comp__b3759ba9d99b
