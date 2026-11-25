-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mk_mem_kerPtQ
-- name    : ReciprocityTheory.AnForm.R.mk_mem_kerPtQ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:02.09602+00:00
-- url     : https://prove2.me/theorems/c966eef6-f582-4ffa-bd7c-cae9dcf32bab
-- title:
--   R: mk mem ker Pt Q
-- statement:
--   The R construction uses the mk mem ker Pt Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjHypStalk.lean#L24-L26

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypStalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {σ : Type}

theorem ReciprocityTheory.AnForm.R.mk_mem_kerPtQ {I : Ideal (MvPolynomial σ ℂ)} {z : σ → ℂ} (hI : I ≤ kerPt z)
    (f : MvPolynomial σ ℂ) : Ideal.Quotient.mk I f ∈ kerPtQ I z ↔ f ∈ kerPt z := by sorry
