-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PosProof_jr_pos
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PosProof.jr_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:06.684059+00:00
-- url     : https://prove2.me/theorems/f9e7213d-8ea0-41ac-955d-d5fab488f1c4
-- title:
--   Pos Proof: jr pos
-- statement:
--   The Pos Proof construction uses the jr pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/IntegralHkDiag.lean#L93-L102

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_IntegralHkDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Module
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.PosProof

theorem PositivityTheory.Rg.Sw.FFTSteps.PosProof.jr_pos (k : ℕ) : 0 < jr k := by sorry
