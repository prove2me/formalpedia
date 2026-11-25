-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_core
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.core
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:26.595803+00:00
-- url     : https://prove2.me/theorems/b1ef97b9-a352-4270-8e4c-760be8ed3601
-- title:
--   Pow Span B: core
-- statement:
--   The Pow Span B construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L92-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L92-L120

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

theorem PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.core : ∀ l : List (PX m n), (∀ v ∈ l, v ∈ W ε) → ∀ w ∈ W ε, ∀ r : ℕ, l.prod * w ^ r ∈ S ε := by sorry
