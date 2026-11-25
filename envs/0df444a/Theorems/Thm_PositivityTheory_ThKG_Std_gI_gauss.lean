-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_gI_gauss
-- name    : PositivityTheory.ThKG.Std.gI_gauss
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:04:06.408903+00:00
-- url     : https://prove2.me/theorems/e697c684-2116-4409-9d9b-23c6b6e864be
-- title:
--   Std: g I gauss
-- statement:
--   The Std construction uses the g I gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L213-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L213-L251

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_ContinuousCut
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Pointwise
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
open Classical

theorem PositivityTheory.ThKG.Std.gI_gauss (hm : IsVol m) (hψ : IsPsi ψ) (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) [Fintype (Res k c)ˣ] :
    gI m ψ ν (((ϖ : k) ^ c)⁻¹) = ((resCard k : ℂ) ^ c)⁻¹ * ∑ y : (Res k c)ˣ,
      if h : ((Quotient.out y.1 : 𝒪[k]) : k) = 0 then 0 else
        (((ν (Units.mk0 _ h))⁻¹ : ℂˣ) : ℂ) * ψ (((Quotient.out y.1 : 𝒪[k]) : k) / ϖ ^ c) := by sorry
