-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AsmA_pair_inv
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AsmA.pair_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:33.273374+00:00
-- url     : https://prove2.me/theorems/3907c833-d765-455d-b829-70e3f5b68fdc
-- title:
--   Asm A: pair inv
-- statement:
--   The Asm A construction uses the pair inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean#L49-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyTB.lean#L49-L76

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
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
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.AsmA.pair_inv {q : PV ι A B} (hq : q ∈ pairAlg ι A B) : IsInv q := by sorry
