-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_pp_trunc
-- name    : ReciprocityTheory.Coh.CCA.pp_trunc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:21.763514+00:00
-- url     : https://prove2.me/theorems/bed4fdab-e17d-5f87-a925-0cea77b870f4
-- title:
--   CCA: pp trunc
-- statement:
--   The CCA construction uses the pp trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L86-L90

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

theorem ReciprocityTheory.Coh.CCA.pp_trunc {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) (k : Fin (p + 1)) :
    Fin.partialProd (fun i : Fin p => g (Fin.castAdd q i)) k = Fin.partialProd g ⟨k, by omega⟩ := by sorry
