-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AvgPf_continuous_coeff_sub
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AvgPf.continuous_coeff_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:55.68289+00:00
-- url     : https://prove2.me/theorems/69cc02b0-89e9-4f4a-9e66-6657be67e5e7
-- title:
--   Avg Pf: continuous coeff sub
-- statement:
--   The Avg Pf construction uses the continuous coeff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean#L47-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean#L47-L79

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousCoeffSub
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.AvgPf
variable {ι A B : Type} [Fintype ι]

theorem PositivityTheory.Rg.Sw.FFTSteps.AvgPf.continuous_coeff_sub {K : Type} [TopologicalSpace K] (g h : K → Matrix ι ι ℂ) (hg : Continuous g)
    (hh : Continuous h) (p : PV ι A B) : ∀ m, Continuous fun k => coeff m (sub (g k) (h k) p) := by sorry
