-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_residueFieldMap_constRes
-- name    : ReciprocityTheory.AnForm.R.residueFieldMap_constRes
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:27.452613+00:00
-- url     : https://prove2.me/theorems/fbb58276-10ef-57d3-aa0e-0cbbffe820a9
-- title:
--   R: residue Field Map const Res
-- statement:
--   The R construction uses the residue Field Map const Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L97-L111

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

theorem ReciprocityTheory.AnForm.R.residueFieldMap_constRes {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) (x : S) :
    (g.residueFieldMap x).hom.comp (constRes t (g.base x)) = constRes s x := by sorry
