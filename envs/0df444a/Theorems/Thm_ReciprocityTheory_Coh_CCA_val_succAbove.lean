-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_val_succAbove
-- name    : ReciprocityTheory.Coh.CCA.val_succAbove
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:57.918802+00:00
-- url     : https://prove2.me/theorems/485ac9a3-2ee4-4e9f-939f-1b131178df2f
-- title:
--   CCA: val succ Above
-- statement:
--   The CCA construction uses the val succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L20-L25

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]

theorem ReciprocityTheory.Coh.CCA.val_succAbove {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    (i.succAbove k : ℕ) = if (k : ℕ) < i then (k : ℕ) else k + 1 := by sorry
