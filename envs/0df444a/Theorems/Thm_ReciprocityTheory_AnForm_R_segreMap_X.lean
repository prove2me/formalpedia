-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_segreMap_X
-- name    : ReciprocityTheory.AnForm.R.segreMap_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:07.504019+00:00
-- url     : https://prove2.me/theorems/1ce96634-c505-4103-a5d6-3e6b53685f0a
-- title:
--   R: segre Map X
-- statement:
--   The R construction uses the segre Map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L53-L55

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.segreMap_X (p : (k : K) → ι k) :
    segreMap (X p : MvPolynomial ((k : K) → ι k) ℂ) = ∏ k, X ⟨k, p k⟩ := by sorry
