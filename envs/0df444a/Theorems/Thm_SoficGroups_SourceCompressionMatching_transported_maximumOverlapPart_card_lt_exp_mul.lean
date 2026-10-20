-- Prove2me | Theorems.Thm_SoficGroups_SourceCompressionMatching_transported_maximumOverlapPart_card_lt_exp_mul
-- name    : SoficGroups.SourceCompressionMatching.transported_maximumOverlapPart_card_lt_exp_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/056f6249-4042-4739-b816-ef8f96ab1a40
-- title:
--   SoficGroups.SourceCompressionMatching.transported_maximumOverlapPart_card_lt_exp_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceCompressionMatching.transported_maximumOverlapPart_card_lt_exp_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (C : Finset V) (hC : C ∈ Q.parts)
    (H r : ℝ) (hH : 0 < H) (x : V) (hx : x ∈ C)
    (hTx : T x ∈ SoficGroups.maximumOverlapPart Q
      (C.map T.toEmbedding))
    (hrank :
      SoficGroups.MidrankPermutationEnergy.offsetFloorRank
          (fun z : V =>
            Real.log (SoficGroups.partitionComponentSize Q z : ℝ))
          H r (T x) =
        SoficGroups.MidrankPermutationEnergy.offsetFloorRank
          (fun z : V =>
            Real.log (SoficGroups.partitionComponentSize Q z : ℝ))
          H r x) :
    ((SoficGroups.maximumOverlapPart Q
      (C.map T.toEmbedding)).card : ℝ) <
        Real.exp H * (C.card : ℝ) := by sorry
