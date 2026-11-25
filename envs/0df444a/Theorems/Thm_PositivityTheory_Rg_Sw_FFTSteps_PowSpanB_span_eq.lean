-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_span_eq
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.span_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:41.885801+00:00
-- url     : https://prove2.me/theorems/8c3c6785-c519-461c-8134-f903bde88d04
-- title:
--   Pow Span B: span eq
-- statement:
--   The Pow Span B construction uses the span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L153-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L153-L177

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

theorem PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.span_eq :
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule = S ε := by sorry
