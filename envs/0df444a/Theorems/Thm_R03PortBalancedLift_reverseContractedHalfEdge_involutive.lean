-- Prove2me | Theorems.Thm_R03PortBalancedLift_reverseContractedHalfEdge_involutive
-- name    : R03PortBalancedLift.reverseContractedHalfEdge_involutive
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:23:48.102036+00:00
-- url     : https://prove2.me/theorems/ce10ed7b-eb2c-43da-af68-7412e9b2f6e4
-- title:
--   R03 P3-factor structural result: Reverse contracted half edge involutive
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03PortBalancedLift.reverseContractedHalfEdge_involutive` under exactly the explicit hypotheses in the Lean statement. It is a reusable conditional result and does not claim closure of the open root problem.
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
theorem reverseContractedHalfEdge_involutive (z : Σ p : P, Σ b : Fin 2, P × Fin 2) :
    reverseContractedHalfEdge (reverseContractedHalfEdge z) = z := by sorry

end R03PortBalancedLift
