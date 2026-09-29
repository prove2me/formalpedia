-- Prove2me | Theorems.Thm_R03PortBalancedLift_pairingGraph_perfectMatching
-- name    : R03PortBalancedLift.pairingGraph_perfectMatching
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:24:02.924159+00:00
-- url     : https://prove2.me/theorems/6ef02e15-e668-4020-b7ca-fa86f6c879c0
-- title:
--   R03 P3-factor structural result: Pairing graph perfect matching
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03PortBalancedLift.pairingGraph_perfectMatching` under exactly the explicit hypotheses in the Lean statement. It is a reusable conditional result and does not claim closure of the open root problem.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp05/sp05_port_balanced_quotient_lift_formalization_v1.lean; source SHA-256 57fa222021aa425ec2411a888cc409befe235b123a468d11050269c21de596ab; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_2164cbfb81_sp05_port_balanced_quotient_lift_formalization_v

namespace R03PortBalancedLift

open R03PortBalancedLift
open CubicP3Partition
universe u v
variable {P : Type u} {V : Type v} [Fintype P] [Fintype V]
open scoped Classical
theorem pairingGraph_perfectMatching
    (G : SimpleGraph V) (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))) :
    PerfectMatching G (pairingGraph pair) := by sorry

end R03PortBalancedLift
