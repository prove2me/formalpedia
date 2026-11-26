-- Prove2me | Theorems.Thm_SharpIntermediateSubgroupBounds_exists_sylow_pretransitive_of_index_primePower
-- name    : SharpIntermediateSubgroupBounds.exists_sylow_pretransitive_of_index_primePower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:49:47.731313+00:00
-- url     : https://prove2.me/theorems/77819ef7-fd4d-53d1-8f7f-90164883f031
-- title:
--   Sharp Intermediate Subgroup Bounds: exists sylow pretransitive of index prime Power
-- statement:
--   If `[G:H]` is a power of `p`, a Sylow `p`-subgroup of `G` can be chosen so that its
--   action on `G/H` is transitive.  Its stabilizer has exactly the same prime-power index.
--
--   Source: https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L382-L458
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/PrimePower.lean#L382-L458

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

theorem SharpIntermediateSubgroupBounds.exists_sylow_pretransitive_of_index_primePower {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    ∃ P : Sylow p G,
      MulAction.IsPretransitive P (G ⧸ H) ∧ H.relIndex (P : Subgroup G) = p ^ a := by sorry
