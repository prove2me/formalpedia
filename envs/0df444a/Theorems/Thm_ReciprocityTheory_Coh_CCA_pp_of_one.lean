-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_pp_of_one
-- name    : ReciprocityTheory.Coh.CCA.pp_of_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:04.470666+00:00
-- url     : https://prove2.me/theorems/8d5fb770-e680-4ead-8d5f-ba37ddc25390
-- title:
--   CCA: pp of one
-- statement:
--   The CCA construction uses the pp of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L105-L109

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

theorem ReciprocityTheory.Coh.CCA.pp_of_one {K : Type*} [Group K] {n : ℕ} (t : Fin (n + 1) → K) (h0 : t 0 = 1) (k : Fin (n + 1)) :
    Fin.partialProd (fun i : Fin n => (t i.castSucc)⁻¹ * t i.succ) k = t k := by sorry
