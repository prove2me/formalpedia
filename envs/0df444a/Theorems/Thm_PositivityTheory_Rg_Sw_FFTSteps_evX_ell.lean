-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_evX_ell
-- name    : PositivityTheory.Rg.Sw.FFTSteps.evX_ell
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:50.707533+00:00
-- url     : https://prove2.me/theorems/89a1051c-d29d-4860-96b0-9818862f94a7
-- title:
--   FFTSteps: ev X ell
-- statement:
--   The FFTSteps construction uses the ev X ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/NullTop.lean#L149-L151

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.FFTSteps.evX_ell (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x = (b * gramX ε x).trace := by sorry
