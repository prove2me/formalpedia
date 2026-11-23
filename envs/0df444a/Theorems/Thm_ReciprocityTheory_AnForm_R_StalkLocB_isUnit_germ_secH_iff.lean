-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_isUnit_germ_secH_iff
-- name    : ReciprocityTheory.AnForm.R.StalkLocB.isUnit_germ_secH_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:32.758317+00:00
-- url     : https://prove2.me/theorems/7932b498-1dd5-4428-9173-bf6d934b9698
-- title:
--   Stalk Loc B: is Unit germ sec H iff
-- statement:
--   The Stalk Loc B construction uses the is Unit germ sec H iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L51-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L51-L84

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

theorem ReciprocityTheory.AnForm.R.StalkLocB.isUnit_germ_secH_iff (v : V) (f : MvPolynomial (Fin n) ℂ) :
    IsUnit (W.presheaf.germ V v.1 v.2 (secH V K iso f)) ↔
      Ideal.Quotient.mk K f ∉ (iso.hom.base v).asIdeal := by sorry
