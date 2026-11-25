-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Coh_cont_cons__f1a3f8bb1a53
-- name    : P2M_ReciprocityTheory_Coh_cont_cons__f1a3f8bb1a53
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:17:03.898684+00:00
-- url     : https://prove2.me/theorems/a9b1f51e-8179-5fda-b002-0307fcd31fbc
-- title:
--   P2 M Reciprocity Theory Coh cont cons  f1a3f8bb1a53: P2 M Reciprocity Theory Coh cont cons  f1a3f8bb1a53
-- statement:
--   The P2 M Reciprocity Theory Coh cont cons  f1a3f8bb1a53 construction uses the P2 M Reciprocity Theory Coh cont cons  f1a3f8bb1a53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/PrismOpZeroEval.lean#L176-L178

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

theorem P2M_ReciprocityTheory_Coh_cont_cons__f1a3f8bb1a53 {S Y : Type*} [TopologicalSpace S] [TopologicalSpace Y] {m : ℕ} (f : S → Y)
    (g : S → Fin m → Y) (hf : Continuous f) (hg : Continuous g) :
    Continuous fun s => (Fin.cons (f s) (g s) : Fin (m + 1) → Y) := by sorry

alias «ReciprocityTheory».«Coh».«cont_cons'» := P2M_ReciprocityTheory_Coh_cont_cons__f1a3f8bb1a53
