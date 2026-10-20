-- Prove2me | Theorems.Thm_SoficGroups_partitionComponentSize_transport_lower_of_retained
-- name    : SoficGroups.partitionComponentSize_transport_lower_of_retained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/0975544e-46ba-4c48-a189-ccd979f5baac
-- title:
--   SoficGroups.partitionComponentSize_transport_lower_of_retained
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.partitionComponentSize_transport_lower_of_retained
    {V : Type u} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (C : Finset V) (hC : C ∈ Q.parts)
    (eta : ℝ)
    (hretained : C.map T.toEmbedding ∉
      insufficientOverlapComponents
        (transportedUnivFinpartition Q T) Q eta)
    (x : V) (hx : x ∈ C)
    (hTx : T x ∈ maximumOverlapPart Q (C.map T.toEmbedding)) :
    (1 - eta) * (partitionComponentSize Q x : ℝ) ≤
      (partitionComponentSize Q (T x) : ℝ) := by sorry
