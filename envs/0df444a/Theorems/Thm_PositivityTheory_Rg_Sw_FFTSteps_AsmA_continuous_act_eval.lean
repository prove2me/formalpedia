-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_continuous_act_eval
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmA.continuous_act_eval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:39.015243+00:00
-- url     : https://prove2.me/theorems/c13baa02-6d45-4f99-98b5-2a6c9bbd5e6d
-- title:
--   Asm A: continuous act eval
-- statement:
--   The Asm A construction uses the continuous act eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean#L45-L53

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
variable {ι A B : Type} [Fintype ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmA.continuous_act_eval {X : Type} [TopologicalSpace X] {F G : X → Matrix ι ι ℂ} (hF : Continuous F)
    (hG : Continuous G) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    Continuous fun x => eval (act (F x) (G x) z) p := by sorry
