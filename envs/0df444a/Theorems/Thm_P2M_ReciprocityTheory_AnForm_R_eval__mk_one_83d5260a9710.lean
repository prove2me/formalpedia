-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_eval__mk_one_83d5260a9710
-- name    : P2M_ReciprocityTheory_AnForm_R_eval__mk_one_83d5260a9710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:09.954448+00:00
-- url     : https://prove2.me/theorems/a26dd456-c84a-4f8a-bed2-911e3f9b5696
-- title:
--   P2 M Reciprocity Theory An Form R eval  mk one 83d5260a9710: P2 M Reciprocity Theory An Form R eval  mk one 83d5260a9710
-- statement:
--   The P2 M Reciprocity Theory An Form R eval  mk one 83d5260a9710 construction uses the P2 M Reciprocity Theory An Form R eval  mk one 83d5260a9710 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L144-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L144-L154

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_ReciprocityTheory_AnForm_R_eval__mk_one_83d5260a9710 {τ : Type} (I : Ideal (MvPolynomial τ ℂ)) (M : Submonoid (MvPolynomial τ ℂ ⧸ I))
    {σ : Type} (Y : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval₂ (algebraMap ℂ (Localization M)) (fun q => Localization.mk (Ideal.Quotient.mk I (Y q)) 1) f =
      Localization.mk (Ideal.Quotient.mk I (aeval Y f)) 1 := by sorry

alias «ReciprocityTheory».«AnForm».«R».«eval₂_mk_one» := P2M_ReciprocityTheory_AnForm_R_eval__mk_one_83d5260a9710
