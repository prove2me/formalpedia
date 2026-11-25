-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_ringHom
-- name    : ReciprocityTheory.AnForm.R.val_ringHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:09.808019+00:00
-- url     : https://prove2.me/theorems/849ed4ae-d551-4168-ac95-8e8cfdcb4d2d
-- title:
--   R: val ring Hom
-- statement:
--   The R construction uses the val ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L120-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))

theorem ReciprocityTheory.AnForm.R.val_ringHom [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    ∃ φ : Γ(S, U) →+* ℂ, ∀ f, φ f = val s f x hx := by sorry
