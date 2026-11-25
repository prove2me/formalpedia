-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_emb_pair
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.emb_pair
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:45.607909+00:00
-- url     : https://prove2.me/theorems/8e65cda5-e1b7-4821-b228-ec64ecca4de3
-- title:
--   Cyc F: emb pair
-- statement:
--   The Cyc F construction uses the emb pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L51-L55

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

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.emb_pair (β : Bool) (a b : Fin n) :
    emb ε β (∑ i : Rw ε β, (X (Sum.inl (i, a)) : PV (Rw ε β) (Fin n) (Fin n)) * X (Sum.inr (i, b))) = Qb ε β b a := by sorry
