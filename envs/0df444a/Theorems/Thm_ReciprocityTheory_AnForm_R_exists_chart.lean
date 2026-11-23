-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_chart
-- name    : ReciprocityTheory.AnForm.R.exists_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:22.49077+00:00
-- url     : https://prove2.me/theorems/2083456d-0c10-4676-926f-67e87a190e4e
-- title:
--   R: exists chart
-- statement:
--   The R construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L108-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean#L108-L121

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

theorem ReciprocityTheory.AnForm.R.exists_chart (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ p : (k : K) → ι k, (∀ k, z ⟨k, p k⟩ ≠ 0) ∧ ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, p k⟩‖ := by sorry
