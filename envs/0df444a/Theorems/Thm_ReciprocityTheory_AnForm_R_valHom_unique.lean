-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_unique
-- name    : ReciprocityTheory.AnForm.R.valHom_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:17.041399+00:00
-- url     : https://prove2.me/theorems/27baca95-71e2-45c7-86cb-fdc83e46dec7
-- title:
--   R: val Hom unique
-- statement:
--   The R construction uses the val Hom unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L52-L61

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

theorem ReciprocityTheory.AnForm.R.valHom_unique [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S))
    (ψ : S.residueField x →+* ℂ) (h : ψ.comp (constRes s x) = RingHom.id ℂ) :
    ψ = (residueFieldIsoBase s x hx).hom.hom := by sorry
