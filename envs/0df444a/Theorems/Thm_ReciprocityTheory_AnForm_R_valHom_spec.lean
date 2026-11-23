-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_spec
-- name    : ReciprocityTheory.AnForm.R.valHom_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:52.164849+00:00
-- url     : https://prove2.me/theorems/a023b4d4-7867-4c18-ba9b-6857bc30e91a
-- title:
--   R: val Hom spec
-- statement:
--   The R construction uses the val Hom spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L63-L65

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

theorem ReciprocityTheory.AnForm.R.valHom_spec [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    ((residueFieldIsoBase s x hx).hom.hom).comp (constRes s x) = RingHom.id ℂ := by sorry
