-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Std_res_eq_iff
-- name    : PositivityTheory.ThKG.Std.res_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:09.292719+00:00
-- url     : https://prove2.me/theorems/1866a4c5-821b-4283-ba27-08b41bcc36ef
-- title:
--   Std: res eq iff
-- statement:
--   The Std construction uses the res eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L173-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/IntIndPow.lean#L173-L177

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
omit [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k]

theorem PositivityTheory.ThKG.Std.res_eq_iff (hϖ : IsUnif ϖ) (c : ℕ) (x y : 𝒪[k]) :
    (Ideal.Quotient.mk _ x : Res k c) = Ideal.Quotient.mk _ y ↔ valuation k ((x : k) - y) ≤ valuation k ((ϖ : k) ^ c) := by sorry
