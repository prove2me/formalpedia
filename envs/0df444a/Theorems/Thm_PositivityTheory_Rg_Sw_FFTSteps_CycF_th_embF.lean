-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_embF
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.th_embF
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:41.463913+00:00
-- url     : https://prove2.me/theorems/6ee949b1-0161-4617-adde-799f4e9b636e
-- title:
--   Cyc F: th emb F
-- statement:
--   The Cyc F construction uses the th emb F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L42-L54

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

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.th_embF (t : PV (Rw ε false) (Fin n) (Fin n)) :
    Th ε (emb ε false t) = map (algebraMap ℂ (PV (Rw ε true) (Fin n) (Fin n))) t := by sorry
