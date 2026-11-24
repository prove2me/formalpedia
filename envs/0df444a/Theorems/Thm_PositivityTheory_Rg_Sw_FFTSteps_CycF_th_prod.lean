-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_prod
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.th_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:41.666802+00:00
-- url     : https://prove2.me/theorems/1022a40e-2c90-463e-a474-f30063546165
-- title:
--   Cyc F: th prod
-- statement:
--   The Cyc F construction uses the th prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L56-L58

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
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
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.th_prod (c : PV (Rw ε true) (Fin n) (Fin n)) (μ : VV (Rw ε false) n →₀ ℕ) :
    Th ε (emb ε true c * emb ε false (monomial μ 1)) = monomial μ c := by sorry
