-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmT_act_ren
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmT.act_ren
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:15.546384+00:00
-- url     : https://prove2.me/theorems/c1109590-5006-4880-9754-62ffe173d65a
-- title:
--   Asm T: act ren
-- statement:
--   The Asm T construction uses the act ren property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean#L63-L70

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmT.act_ren (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    (act u (u.map star) (fun v => eval z (resφ ι v))) ∘ ren = act (blk u) ((blk u).map star) z := by sorry
