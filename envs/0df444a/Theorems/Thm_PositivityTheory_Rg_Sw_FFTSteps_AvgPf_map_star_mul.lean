-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_AvgPf_map_star_mul
-- name    : PositivityTheory.Rg.Sw.FFTSteps.AvgPf.map_star_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:51.769+00:00
-- url     : https://prove2.me/theorems/1c1e0c3f-a805-5f99-b98d-86d340a6f514
-- title:
--   Avg Pf: map star mul
-- statement:
--   The Avg Pf construction uses the map star mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean#L91-L93

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

theorem PositivityTheory.Rg.Sw.FFTSteps.AvgPf.map_star_mul {N : ℕ} (a b : Matrix (Fin N) (Fin N) ℂ) : (a * b).map star = a.map star * b.map star := by sorry
