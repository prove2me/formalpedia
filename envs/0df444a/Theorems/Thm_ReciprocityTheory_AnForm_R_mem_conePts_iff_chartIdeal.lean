-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mem_conePts_iff_chartIdeal
-- name    : ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:35.10798+00:00
-- url     : https://prove2.me/theorems/c1dfcf18-caf7-4dea-b651-bd8c32b2b3e5
-- title:
--   R: mem cone Pts iff chart Ideal
-- statement:
--   The R construction uses the mem cone Pts iff chart Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L52-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L52-L85

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
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

theorem ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    z ∈ conePts P ↔ ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 := by sorry
