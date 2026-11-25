-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_single
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:33.375741+00:00
-- url     : https://prove2.me/theorems/d7d25b42-d2c4-46a9-ac2d-3fd28abd6305
-- title:
--   Pow Span B: lf single
-- statement:
--   The Pow Span B construction uses the lf single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L26-L27

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_PowSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
open PositivityTheory.Rg.Sw.FFTSteps.PowSpanB
variable {m n : ℕ} (ε : Fin m → Bool)

theorem PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_single (a b : Fin n) : lf ε (Matrix.single b a (1 : ℂ)) = (Qp ε a b : PX m n) := by sorry
