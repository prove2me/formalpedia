-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_local_step
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.local_step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:49.512426+00:00
-- url     : https://prove2.me/theorems/259c3b15-def8-5eea-aa64-d1447c3ab466
-- title:
--   Div LA: local step
-- statement:
--   The Div LA construction uses the local step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLD.lean#L32-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLD.lean#L32-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.local_step {δ T d : ℕ} (hd : d ≤ T) (W : V n → ℂ) (S : Fin n → V n → ℂ)
    (Tt : Fin δ → V n → ℂ) (L : V n ≃L[ℂ] V n)
    (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0) (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hT : ∀ k, AnalyticAt ℂ (Tt k) 0)
    (hL : ∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z)
    (G : V n → ℂ) (hG : AnalyticAt ℂ G 0) (hGO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ c : (Fin n → ℕ) → Fin δ → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ k, c α k * Tt k 0 * W 0 ^ T = a α) →
      (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by sorry
