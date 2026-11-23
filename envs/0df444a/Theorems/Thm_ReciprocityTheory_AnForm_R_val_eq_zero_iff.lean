-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_eq_zero_iff
-- name    : ReciprocityTheory.AnForm.R.val_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:57.63697+00:00
-- url     : https://prove2.me/theorems/7a66c355-37ef-4af3-a786-d1f1a43535f8
-- title:
--   R: val eq zero iff
-- statement:
--   The R construction uses the val eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L139-L143

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

theorem ReciprocityTheory.AnForm.R.val_eq_zero_iff [LocallyOfFiniteType s] {U : S.Opens} (f : Γ(S, U)) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) : val s f x hx = 0 ↔ S.evaluation U x hx f = 0 := by sorry
