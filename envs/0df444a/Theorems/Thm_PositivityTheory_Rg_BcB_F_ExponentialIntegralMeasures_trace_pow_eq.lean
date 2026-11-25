-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_trace_pow_eq
-- name    : PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.trace_pow_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:50.250341+00:00
-- url     : https://prove2.me/theorems/d6c301f1-67f9-40bf-978c-93a82f785b5e
-- title:
--   Exponential Integral Measures: trace pow eq
-- statement:
--   The Exponential Integral Measures construction uses the trace pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L101-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L101-L134

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures

theorem PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.trace_pow_eq {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hfin : {μ | T.maxGenEigenspace μ ≠ ⊥}.Finite) (k : ℕ) :
    LinearMap.trace ℂ V (T ^ k) =
      ∑ μ ∈ hfin.toFinset, (Module.finrank ℂ (T.maxGenEigenspace μ) : ℂ) * μ ^ k := by sorry
