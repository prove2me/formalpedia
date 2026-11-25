-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_sub__b0a4dbfa4590
-- name    : P2M_ReciprocityTheory_Coh_hd_sub__b0a4dbfa4590
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:27.275893+00:00
-- url     : https://prove2.me/theorems/79a89286-7351-4222-a3dd-1dfd3f8d5cf4
-- title:
--   P2 M Reciprocity Theory Coh hd sub  b0a4dbfa4590: P2 M Reciprocity Theory Coh hd sub  b0a4dbfa4590
-- statement:
--   The P2 M Reciprocity Theory Coh hd sub  b0a4dbfa4590 construction uses the P2 M Reciprocity Theory Coh hd sub  b0a4dbfa4590 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L44-L46

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

theorem P2M_ReciprocityTheory_Coh_hd_sub__b0a4dbfa4590 (n : ℕ) (F G : (Fin (n + 1) → X) → V) (x : Fin (n + 2) → X) :
    hd n (fun y => F y - G y) x = hd n F x - hd n G x := by sorry

alias «ReciprocityTheory».«Coh».«hd_sub'» := P2M_ReciprocityTheory_Coh_hd_sub__b0a4dbfa4590
