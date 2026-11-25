-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_pp_tail
-- name    : ReciprocityTheory.Coh.CCA.pp_tail
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:58.297642+00:00
-- url     : https://prove2.me/theorems/28030657-a4d3-4022-a849-792817c4f34b
-- title:
--   CCA: pp tail
-- statement:
--   The CCA construction uses the pp tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L98-L103

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

theorem ReciprocityTheory.Coh.CCA.pp_tail {K : Type*} [Group K] {p q : ℕ} (g : Fin (p + q) → K) (j : Fin q) :
    (Fin.partialProd g ⟨p + j, by omega⟩)⁻¹ * Fin.partialProd g ⟨p + j + 1, by omega⟩ =
      g (Fin.natAdd p j) := by sorry
