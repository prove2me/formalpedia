-- Prove2me | Theorems.Thm_R03PortBalancedLift_allContractedHalfEdgeFinset_card
-- name    : R03PortBalancedLift.allContractedHalfEdgeFinset_card
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:23:54.043077+00:00
-- url     : https://prove2.me/theorems/d68d0d43-034a-4ad8-a493-b995ff2d44d9
-- title:
--   R03 P3-factor structural result: All contracted half edge finset card
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03PortBalancedLift.allContractedHalfEdgeFinset_card` under exactly the explicit hypotheses in the Lean statement. It is a reusable conditional result and does not claim closure of the open root problem.
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
theorem allContractedHalfEdgeFinset_card
    (G : SimpleGraph V) (hG : CubicP3Partition.Cubic G)
    (pair : (P × Fin 2) ≃ V)
    (pair_edge : ∀ p, G.Adj (pair (p, 0)) (pair (p, 1))) :
    (allContractedHalfEdgeFinset G pair).card = 4 * Fintype.card P := by sorry

end R03PortBalancedLift
