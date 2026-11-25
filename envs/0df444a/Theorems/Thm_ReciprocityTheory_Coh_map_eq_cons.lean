-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_map_eq_cons
-- name    : ReciprocityTheory.Coh.map_eq_cons
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:21.2578+00:00
-- url     : https://prove2.me/theorems/a6745b57-8092-40fc-9c5e-99e93e31dae7
-- title:
--   Coh: map eq cons
-- statement:
--   The Coh construction uses the map eq cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L85-L88

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

theorem ReciprocityTheory.Coh.map_eq_cons (b : X → Y) {n : ℕ} (x : Fin (n + 1) → X) :
    (fun j => b (x j)) = Fin.cons (b (x 0)) fun j => b (Fin.tail x j) := by sorry
