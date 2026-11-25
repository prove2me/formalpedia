-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_iter_fQ
-- name    : PositivityTheory.Rg.Sw.SP.iter_fQ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:33.300144+00:00
-- url     : https://prove2.me/theorems/33990b9f-9716-5171-8b3d-e3a2f8c028c1
-- title:
--   SP: iter f Q
-- statement:
--   The SP construction uses the iter f Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L39-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L39-L52

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.iter_fQ (s : ℂ) (hs : s = 1 ∨ s = -1) (z : ℂ) (m : ℕ) :
    ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n) (x : MC n), x ∈ OmS s →
      iteratedFDeriv ℂ k (fQ s z m Q) x (fun i => eU (dirs i).1 (dirs i).2) = fQ s z m (opsSeq s m k dirs Q) x
  := by sorry
