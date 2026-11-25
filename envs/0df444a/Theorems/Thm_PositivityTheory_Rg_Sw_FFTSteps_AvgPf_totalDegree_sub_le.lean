-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AvgPf_totalDegree_sub_le
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AvgPf.totalDegree_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:47.587265+00:00
-- url     : https://prove2.me/theorems/8e7fee31-2748-5726-9ab3-3c8e643bd77b
-- title:
--   Avg Pf: total Degree sub le
-- statement:
--   The Avg Pf construction uses the total Degree sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean#L44-L45

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

theorem PositivityTheory.Rg.Sw.FFTSteps.AvgPf.totalDegree_sub_le (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree := by sorry
