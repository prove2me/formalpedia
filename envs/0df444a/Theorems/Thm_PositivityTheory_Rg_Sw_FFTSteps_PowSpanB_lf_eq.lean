-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_PowSpanB_lf_eq
-- name    : PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:55:13.940263+00:00
-- url     : https://prove2.me/theorems/0ed23238-abe0-4728-b5fe-561fb0775f1d
-- title:
--   Pow Span B: lf eq
-- statement:
--   The Pow Span B construction uses the lf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/PowSpan.lean#L16-L18

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

theorem PositivityTheory.Rg.Sw.FFTSteps.PowSpanB.lf_eq (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) = lf ε b := by sorry
