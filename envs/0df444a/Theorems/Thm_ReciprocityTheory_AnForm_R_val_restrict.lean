-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_val_restrict
-- name    : ReciprocityTheory.AnForm.R.val_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:33.698382+00:00
-- url     : https://prove2.me/theorems/9a816388-0ccc-47d4-93f0-a2c5e949b224
-- title:
--   R: val restrict
-- statement:
--   The R construction uses the val restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/FromSpecResidueFieldAppTopIso.lean#L134-L137

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

theorem ReciprocityTheory.AnForm.R.val_restrict {U V : S.Opens} (hVU : V ≤ U) (f : Γ(S, U)) (x : S) (hx : x ∈ V) :
    val s (S.presheaf.map (homOfLE hVU).op f) x hx = val s f x (hVU hx) := by sorry
