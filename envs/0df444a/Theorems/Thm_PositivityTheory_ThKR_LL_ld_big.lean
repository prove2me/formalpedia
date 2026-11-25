-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_ld_big
-- name    : PositivityTheory.ThKR.LL.ld_big
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:00.727816+00:00
-- url     : https://prove2.me/theorems/24409126-4e0a-4620-8f26-7470793287bc
-- title:
--   LL: ld big
-- statement:
--   The LL construction uses the ld big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L116-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/NormExpSubLe.lean#L116-L129

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.ld_big {Ai B C : ℝ → Eu l →L[ℝ] Eu l} {Ai' B' C' : Eu l →L[ℝ] Eu l} {c : ℝ → ℝ} {c' t₀ : ℝ}
    (hA : HasDerivAt Ai Ai' t₀) (hB : HasDerivAt B B' t₀) (hC : HasDerivAt C C' t₀) (hc : HasDerivAt c c' t₀)
    (h : ∀ᶠ t in 𝓝 t₀, IsUnit (Ai t) ∧ c t ^ 2 = |(Ai t).det|) :
    ∃ Q, LD (fun t => big (Ai t) (B t) (C t) (c t)) Q t₀ ∧ (Ai t₀ = 1 → B t₀ = 0 → C t₀ = 0 → c t₀ = 1 → ∀ f,
      Q f = mq C' f + vf Ai' f + fou l (mq (-B') (fouInv l f)) + (c' : ℂ) • f) := by sorry
