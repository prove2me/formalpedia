-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_sum_bool_fin
-- name    : PositivityTheory.Rg.Sw.SP.sum_bool_fin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:26.148609+00:00
-- url     : https://prove2.me/theorems/cf1c0455-e2b2-4c02-bf7a-44e0205c9d6e
-- title:
--   SP: sum bool fin
-- statement:
--   The SP construction uses the sum bool fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeC.lean#L36-L40

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.sum_bool_fin (F : Bool × Fin n × Fin n → ℂ) :
    ∑ kk, F kk = ∑ a : Fin n, ∑ d : Fin n, F (false, a, d) + ∑ a : Fin n, ∑ d : Fin n, F (true, a, d) := by sorry
