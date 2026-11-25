-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_opsSeq_eq
-- name    : PositivityTheory.Rg.Sw.SP.opsSeq_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:42.134736+00:00
-- url     : https://prove2.me/theorems/2053a9db-ad56-4ffd-a0c1-28a6748f0caa
-- title:
--   SP: ops Seq eq
-- statement:
--   The SP construction uses the ops Seq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/Bridge.lean#L54-L59

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

theorem PositivityTheory.Rg.Sw.SP.opsSeq_eq (s : ℂ) (m : ℕ) : ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n),
    opsSeq s m k dirs Q = (List.finRange k).foldr (fun i g => opD s m (dirs i).1 (dirs i).2 ∘ₗ g) LinearMap.id Q
  := by sorry
