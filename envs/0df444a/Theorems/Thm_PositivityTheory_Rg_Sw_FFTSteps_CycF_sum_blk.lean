-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_blk
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.sum_blk
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:13.175235+00:00
-- url     : https://prove2.me/theorems/44941fbe-8c1c-4677-af22-69ec989cc797
-- title:
--   Cyc F: sum blk
-- statement:
--   The Cyc F construction uses the sum blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L11-L16

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} {ε : Fin m → Bool}

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.sum_blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (blk ε β v a.1 b) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (v a j) * X (j.1, i, t) := by sorry
