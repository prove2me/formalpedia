-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_eq
-- name    : ReciprocityTheory.AnForm.R.valHom_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:32.455855+00:00
-- url     : https://prove2.me/theorems/2f7849c7-cc07-431c-b2b4-89385d27e5d9
-- title:
--   R: val Hom eq
-- statement:
--   The R construction uses the val Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L67-L72

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

theorem ReciprocityTheory.AnForm.R.valHom_eq [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    valHom s x = (residueFieldIsoBase s x hx).hom.hom := by sorry
