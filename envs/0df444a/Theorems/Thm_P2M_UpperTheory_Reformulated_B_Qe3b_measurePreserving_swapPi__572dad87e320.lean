-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qe3b_measurePreserving_swapPi__572dad87e320
-- name    : P2M_UpperTheory_Reformulated_B_Qe3b_measurePreserving_swapPi__572dad87e320
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:43:35.135941+00:00
-- url     : https://prove2.me/theorems/e7d06872-f22e-5e7a-aecf-2eeecaf8bd8c
-- title:
--   P2 M Upper Theory Reformulated B Qe3b measure Preserving swap Pi  572dad87e320: P2 M Upper Theory Reformulated B Qe3b measure Preserving swap Pi  572dad87e320
-- statement:
--   The P2 M Upper Theory Reformulated B Qe3b measure Preserving swap Pi  572dad87e320 construction uses the P2 M Upper Theory Reformulated B Qe3b measure Preserving swap Pi  572dad87e320 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MeasurePreservingSwapPi.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MeasurePreservingSwapPi.lean#L38-L57

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MeasurePreservingSwapPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qe3b_measurePreserving_swapPi__572dad87e320.{u_1, u_2, u_3} :
    ∀ {ι : Type u_1} {κ : Type u_2} {X : Type u_3} [inst : Fintype ι] [inst_1 : Fintype κ]
    [inst_2 : MeasurableSpace X] (ν : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite ν],
    MeasureTheory.MeasurePreserving (fun (f : ι → κ → X) (k : κ) (i : ι) ↦ f i k)
      (MeasureTheory.Measure.pi fun (x : ι) ↦ MeasureTheory.Measure.pi fun (x : κ) ↦ ν)
      (MeasureTheory.Measure.pi fun (x : κ) ↦ MeasureTheory.Measure.pi fun (x : ι) ↦ ν) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qe3b».«measurePreserving_swapPi».«» := P2M_UpperTheory_Reformulated_B_Qe3b_measurePreserving_swapPi__572dad87e320
