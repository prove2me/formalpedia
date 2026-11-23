-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero
-- name    : ReciprocityTheory.Coh.prismOp_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:28:31.270902+00:00
-- url     : https://prove2.me/theorems/8c3208ed-b874-40bf-895f-c5fb00cd76ff
-- title:
--   Coh: prism Op zero
-- statement:
--   The Coh construction uses the prism Op zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L59-L60

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

theorem ReciprocityTheory.Coh.prismOp_zero (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F (Fin.cons (a (x 0)) fun j => b (x j)) := by sorry
