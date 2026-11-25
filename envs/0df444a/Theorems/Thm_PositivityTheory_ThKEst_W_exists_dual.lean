-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_W_exists_dual
-- name    : PositivityTheory.ThKEst.W.exists_dual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:13.173989+00:00
-- url     : https://prove2.me/theorems/42ecba1b-fc2a-4e5f-897a-3f6401cb86bf
-- title:
--   W: exists dual
-- statement:
--   The W construction uses the exists dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L94-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/RankIffRight.lean#L94-L135

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

theorem PositivityTheory.ThKEst.W.exists_dual (O : ValuationSubring k) (hO : IsCompact (O : Set k)) (hne : ∀ U ∈ 𝓝 (0 : k), ∃ a ≠ 0, a ∈ U)
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {b : k} (hb : ψ b ≠ 1) {V : Set (Matrix (Fin n) (Fin d) k)}
    (hV : V ∈ 𝓝 0) : ∃ (K : Set (Matrix (Fin n) (Fin d) k)) (Λ : OpenAddSubgroup (Matrix (Fin n) (Fin d) k)),
      (∀ Y, Y ∈ Λ ↔ ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1) ∧ (Λ : Set _) ⊆ V := by sorry
