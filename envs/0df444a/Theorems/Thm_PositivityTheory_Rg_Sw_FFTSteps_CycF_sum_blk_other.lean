-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_sum_blk_other
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.sum_blk_other
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:36.729937+00:00
-- url     : https://prove2.me/theorems/7c84d88f-6cf7-4065-b466-c030561e959d
-- title:
--   Cyc F: sum blk other
-- statement:
--   The Cyc F construction uses the sum blk other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L25-L29

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

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.sum_blk_other (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (i : Fin n)
    (t : Bool) (st : Bool) :
    ∑ b, C (if st then star (blk ε β v a b) else blk ε β v a b) * (X (b, i, t) : PX m n) = X (a, i, t) := by sorry
