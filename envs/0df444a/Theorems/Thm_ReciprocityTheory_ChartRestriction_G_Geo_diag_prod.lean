-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_diag_prod
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.diag_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:21.662155+00:00
-- url     : https://prove2.me/theorems/de0ec15a-3d43-4a98-a6fe-101b3c7ebaec
-- title:
--   Geo: diag prod
-- statement:
--   The Geo construction uses the diag prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibB.lean#L33-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFibB.lean#L33-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.diag_prod (d : ℕ) : ∀ e : (Σ k, ι k) → ℕ, (∀ k, ∑ i, e ⟨k, i⟩ = d) →
    ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ d ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ e p = eval (segre z) G := by sorry
