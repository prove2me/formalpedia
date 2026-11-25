-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_existsUnique_valHom
-- name    : ReciprocityTheory.AnForm.R.existsUnique_valHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:15.721587+00:00
-- url     : https://prove2.me/theorems/79bb9b8b-20d2-4112-bc2b-8a02f6c4492f
-- title:
--   R: exists Unique val Hom
-- statement:
--   The R construction uses the exists Unique val Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L113-L118

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

theorem ReciprocityTheory.AnForm.R.existsUnique_valHom [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    (∃! φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ) ∧
      Function.Bijective (valHom s x) := by sorry
