-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_prismOp_one_eval
-- name    : ReciprocityTheory.Coh.prismOp_one_eval
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:26.294837+00:00
-- url     : https://prove2.me/theorems/252d5ae1-12b2-43d6-9a34-af6fbdddd5e7
-- title:
--   Coh: prism Op one eval
-- statement:
--   The Coh construction uses the prism Op one eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L121-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L121-L124

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

theorem ReciprocityTheory.Coh.prismOp_one_eval (a b : X → Y) (K : (Fin 3 → Y) → V) (x : Fin 2 → X) :
    prismOp a b 1 K x = K ![a (x 0), b (x 0), b (x 1)] - K ![a (x 0), a (x 1), b (x 1)] := by sorry
