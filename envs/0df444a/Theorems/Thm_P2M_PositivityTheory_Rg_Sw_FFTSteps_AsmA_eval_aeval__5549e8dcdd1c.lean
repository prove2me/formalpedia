-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c
-- name    : P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:11:18.919915+00:00
-- url     : https://prove2.me/theorems/1590a2e2-8720-46a2-9077-93e204b04ed9
-- title:
--   P2 M Positivity Theory Rg Sw FFTSteps Asm A eval aeval  5549e8dcdd1c: P2 M Positivity Theory Rg Sw FFTSteps Asm A eval aeval  5549e8dcdd1c
-- statement:
--   The P2 M Positivity Theory Rg Sw FFTSteps Asm A eval aeval  5549e8dcdd1c construction uses the P2 M Positivity Theory Rg Sw FFTSteps Asm A eval aeval  5549e8dcdd1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean#L10-L15

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA

theorem P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c {σ τ : Type} (φ : σ → MvPolynomial τ ℂ) (z : τ → ℂ) (p : MvPolynomial σ ℂ) :
    eval z (aeval φ p) = eval (fun v => eval z (φ v)) p := by sorry

alias «PositivityTheory».«Rg».«Sw».«FFTSteps».«AsmA».«eval_aeval'» := P2M_PositivityTheory_Rg_Sw_FFTSteps_AsmA_eval_aeval__5549e8dcdd1c
