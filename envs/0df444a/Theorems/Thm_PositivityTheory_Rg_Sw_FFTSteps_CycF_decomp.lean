-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_decomp
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.decomp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:41:26.324388+00:00
-- url     : https://prove2.me/theorems/2209bb29-35de-4303-b2a5-075cd47331c5
-- title:
--   Cyc F: decomp
-- statement:
--   The Cyc F construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTC.lean#L60-L65

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

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.decomp (Q : PX m n) :
    Q = ∑ μ ∈ (Th ε Q).support, emb ε true ((Th ε Q).coeff μ) * emb ε false (monomial μ 1) := by sorry
