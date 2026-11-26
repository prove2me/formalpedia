-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_card_elementarySubgroup
-- name    : SharpIntermediateSubgroupBounds.card_elementarySubgroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:43:45.296301+00:00
-- url     : https://prove2.me/theorems/3db17c07-c156-5ebd-8d0a-063b1fb82c20
-- title:
--   Sharp Intermediate Subgroup Bounds: card elementary Subgroup
-- statement:
--   A subgroup of an elementary abelian group has cardinality `p` to its
--   linear dimension.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L634-L642
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L634-L642

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype

theorem SharpIntermediateSubgroupBounds.card_elementarySubgroup {p a : ℕ} [Fact p.Prime]
    (Q : Subgroup (Multiplicative (Fin a → ZMod p))) :
    Nat.card Q =
      p ^ Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) := by sorry
