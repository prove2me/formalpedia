-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_emb_pairAlg
-- name    : PositivityTheory.Rg.Sw.FFTSteps.CycF.emb_pairAlg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:55:03.327438+00:00
-- url     : https://prove2.me/theorems/df8d193f-f556-475a-bd7c-fdf1a3dc9070
-- title:
--   Cyc F: emb pair Alg
-- statement:
--   The Cyc F construction uses the emb pair Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/CycFFTB.lean#L57-L63

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

theorem PositivityTheory.Rg.Sw.FFTSteps.CycF.emb_pairAlg (β : Bool) {p : PV (Rw ε β) (Fin n) (Fin n)} (hp : p ∈ pairAlg (Rw ε β) (Fin n) (Fin n)) :
    emb ε β p ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by sorry
