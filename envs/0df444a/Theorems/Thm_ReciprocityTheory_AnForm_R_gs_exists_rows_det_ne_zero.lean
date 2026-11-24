-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_gs_exists_rows_det_ne_zero
-- name    : ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:07.946056+00:00
-- url     : https://prove2.me/theorems/5a186602-6089-4d6d-abff-31852137c076
-- title:
--   R: gs exists rows det ne zero
-- statement:
--   The R construction uses the gs exists rows det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L8-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/GenSmooth.lean#L8-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
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

theorem ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero {K : Type*} [Field K] {t r : ℕ} (M : Matrix (Fin t) (Fin r) K)
    (hM : ∀ c : Fin r → K, M.mulVec c = 0 → c = 0) :
    ∃ a : Fin r → Fin t, (M.submatrix a id).det ≠ 0 := by sorry
