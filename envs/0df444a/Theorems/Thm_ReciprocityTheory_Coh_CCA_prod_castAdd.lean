-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_prod_castAdd
-- name    : ReciprocityTheory.Coh.CCA.prod_castAdd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:26.332998+00:00
-- url     : https://prove2.me/theorems/87dc5203-0b85-5181-b5da-ad5857051db2
-- title:
--   CCA: prod cast Add
-- statement:
--   The CCA construction uses the prod cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L92-L96

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

theorem ReciprocityTheory.Coh.CCA.prod_castAdd {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) :
    (List.ofFn fun i : Fin p => g (Fin.castAdd q i)).prod = Fin.partialProd g ⟨p, by omega⟩ := by sorry
