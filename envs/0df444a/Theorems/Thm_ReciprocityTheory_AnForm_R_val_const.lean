-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_const
-- name    : ReciprocityTheory.AnForm.R.val_const
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:44.493352+00:00
-- url     : https://prove2.me/theorems/8c9cabcd-caab-420a-a132-072bb51b95b1
-- title:
--   R: val const
-- statement:
--   The R construction uses the val const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L128-L132

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

theorem ReciprocityTheory.AnForm.R.val_const [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) (c : ℂ) : val s (constSec s U c) x hx = c := by sorry
