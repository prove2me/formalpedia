-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_exists_cut
-- name    : PositivityTheory.ThKEst.W.exists_cut
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:23.358879+00:00
-- url     : https://prove2.me/theorems/d82322ae-03fb-46b6-abac-de4132152c3f
-- title:
--   W: exists cut
-- statement:
--   The W construction uses the exists cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L137-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L137-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.W
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {n d : ℕ}

theorem PositivityTheory.ThKEst.W.exists_cut [CharZero k] (O : ValuationSubring k) (hO : IsCompact (O : Set k))
    (hne : ∀ U ∈ 𝓝 (0 : k), ∃ a ≠ 0, a ∈ U) (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {b : k} (hb : ψ b ≠ 1)
    {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h0 : ∀ Y, Y.rank ≠ n → f Y = 0) :
    ∃ (m : ℕ) (g : Fin m → Matrix (Fin n) (Fin d) k → ℂ), f = ∑ i, g i ∧ ∀ i, g i ∈ SB _ ∧ (∀ Y, f Y = 0 → g i Y = 0) ∧
      ∃ Y₀, ∀ Z : Matrix (Fin n) (Fin d) k, Z.rank ≠ n → ∃ U : Matrix (Fin n) (Fin d) k,
        (∀ Y, g i Y ≠ 0 → ψ (trace (Y * Uᵀ)) = ψ (trace (Y₀ * Uᵀ))) ∧ ψ (trace ((Z - (Y₀ + Y₀)) * Uᵀ)) ≠ 1 := by sorry
