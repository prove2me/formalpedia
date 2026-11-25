-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_secH_C
-- name    : ReciprocityTheory.AnForm.R.StalkLocB.secH_C
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:15.578354+00:00
-- url     : https://prove2.me/theorems/e1db8f5d-3b4b-5ddd-a75e-2ef829f3e3d4
-- title:
--   Stalk Loc B: sec H C
-- statement:
--   The Stalk Loc B construction uses the sec H C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L87-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L87-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
variable {K iso}

theorem ReciprocityTheory.AnForm.R.StalkLocB.secH_C (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (c : ℂ) :
    secH V K iso (C c) = W.presheaf.map (homOfLE le_top : V ⟶ ⊤).op
      (s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) := by sorry
