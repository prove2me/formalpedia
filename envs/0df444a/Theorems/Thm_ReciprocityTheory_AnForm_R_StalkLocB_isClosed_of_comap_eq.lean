-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_isClosed_of_comap_eq
-- name    : ReciprocityTheory.AnForm.R.StalkLocB.isClosed_of_comap_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:13.554803+00:00
-- url     : https://prove2.me/theorems/a2434c30-a01f-44f5-9714-8231b771b21a
-- title:
--   Stalk Loc B: is Closed of comap eq
-- statement:
--   The Stalk Loc B construction uses the is Closed of comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L118-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L118-L203

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

theorem ReciprocityTheory.AnForm.R.StalkLocB.isClosed_of_comap_eq (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (v : V) (p : Fin n → ℂ)
    (hp : (iso.hom.base v).asIdeal.comap (Ideal.Quotient.mk K) = ptIdeal p) :
    IsClosed ({v.1} : Set W) := by sorry
