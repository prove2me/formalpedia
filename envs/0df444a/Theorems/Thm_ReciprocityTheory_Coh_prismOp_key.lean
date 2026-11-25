-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_prismOp_key
-- name    : ReciprocityTheory.Coh.prismOp_key
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:32.927426+00:00
-- url     : https://prove2.me/theorems/0f550f5e-55de-4a68-ad1a-b2c2527bc201
-- title:
--   Coh: prism Op key
-- statement:
--   The Coh construction uses the prism Op key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L126-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L126-L168

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

theorem ReciprocityTheory.Coh.prismOp_key (a b : X → Y) (n : ℕ) : ∀ (F : (Fin (n + 2) → Y) → V) (x : Fin (n + 2) → X),
    hd n (prismOp a b n F) x + prismOp a b (n + 1) (hd (n + 1) F) x =
      F (fun i => b (x i)) - F (fun i => a (x i)) := by sorry
