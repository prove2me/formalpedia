-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_retr_pull_mem
-- name    : ReciprocityTheory.Coh.CCA.retr_pull_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:31.875399+00:00
-- url     : https://prove2.me/theorems/f92859e9-8403-5310-a8ab-088858039b46
-- title:
--   CCA: retr pull mem
-- statement:
--   The CCA construction uses the retr pull mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L228-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L228-L251

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
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem ReciprocityTheory.Coh.CCA.retr_pull_mem (hU : IsOpen (U : Set G)) {M : TRep R G} (n : ℕ) (F : (Fin (n + 1) → U) → M.V)
    (hF : F ∈ hcoch (M.resSub U) U n) :
    (fun x : Fin (n + 1) → G => F fun i => retr U (x i)) ∈ hcoch (M.resSub U) G n := by sorry
