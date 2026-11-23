-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_evaluation_res
-- name    : ReciprocityTheory.AnForm.R.evaluation_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:25.485912+00:00
-- url     : https://prove2.me/theorems/1bf9bd2b-cb18-4506-8f2e-801d43919bc5
-- title:
--   R: evaluation res
-- statement:
--   The R construction uses the evaluation res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L74-L79

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

theorem ReciprocityTheory.AnForm.R.evaluation_res {U V : S.Opens} (h : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    S.evaluation V x hx (S.presheaf.map (homOfLE h).op f) = S.evaluation U x (h hx) f := by sorry
