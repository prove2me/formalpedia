-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mem_map_renR_iff
-- name    : ReciprocityTheory.AnForm.R.mem_map_renR_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:04.721046+00:00
-- url     : https://prove2.me/theorems/99b5ab2c-aaa5-5d10-a10d-13af6eebec9e
-- title:
--   R: mem map ren R iff
-- statement:
--   The R construction uses the mem map ren R iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LocTransfer.lean#L66-L69

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
noncomputable section
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.mem_map_renR_iff (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial (Fin (Fintype.card σ)) ℂ) :
    h ∈ I.map (renR σ : MvPolynomial σ ℂ →+* _) ↔ (renR σ).symm h ∈ I := by sorry
