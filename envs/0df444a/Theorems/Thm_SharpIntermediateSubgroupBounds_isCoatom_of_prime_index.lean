-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_isCoatom_of_prime_index
-- name    : SharpIntermediateSubgroupBounds.isCoatom_of_prime_index
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:48:42.324364+00:00
-- url     : https://prove2.me/theorems/f18268bf-db41-5e8d-9d41-62f8f6bb1ce2
-- title:
--   Sharp Intermediate Subgroup Bounds: is Coatom of prime index
-- statement:
--   A subgroup of prime index is maximal.  This small lemma is useful below because the
--   prime-index subgroup is chosen by its cardinality, rather than by a maximality argument.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L33-L46
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L33-L46

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

theorem SharpIntermediateSubgroupBounds.isCoatom_of_prime_index (H : Subgroup G) (hprime : H.index.Prime) : IsCoatom H := by sorry
