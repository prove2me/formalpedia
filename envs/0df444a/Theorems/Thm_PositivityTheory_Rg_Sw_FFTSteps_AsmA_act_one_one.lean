-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_act_one_one
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmA.act_one_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:00.435871+00:00
-- url     : https://prove2.me/theorems/769964b3-abd6-4048-a644-710082d538cc
-- title:
--   Asm A: act one one
-- statement:
--   The Asm A construction uses the act one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTA.lean#L41-L43

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

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmA.act_one_one (z : (ι × A) ⊕ (ι × B) → ℂ) [DecidableEq ι] : act (1 : Matrix ι ι ℂ) 1 z = z := by sorry
