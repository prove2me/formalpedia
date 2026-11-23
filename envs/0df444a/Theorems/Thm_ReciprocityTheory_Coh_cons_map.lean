-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_cons_map
-- name    : ReciprocityTheory.Coh.cons_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:54.766529+00:00
-- url     : https://prove2.me/theorems/4abc9b8e-db82-443e-9f23-83e1cd20500e
-- title:
--   Coh: cons map
-- statement:
--   The Coh construction uses the cons map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L81-L83

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

theorem ReciprocityTheory.Coh.cons_map (b : X → Y) {n : ℕ} (x0 : X) (y : Fin n → X) :
    (fun j => b (Fin.cons (α := fun _ => X) x0 y j)) = Fin.cons (b x0) fun j => b (y j) := by sorry
