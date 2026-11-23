-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_sup_of_restrictToSubgroup_mem_sq
-- name    : ReciprocityTheory.PGsh.L2.mem_sup_of_restrictToSubgroup_mem_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:48.069941+00:00
-- url     : https://prove2.me/theorems/ad082188-13b8-4ee1-bb52-a6e852ac048f
-- title:
--   L2: mem sup of restrict To Subgroup mem sq
-- statement:
--   The L2 construction uses the mem sup of restrict To Subgroup mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemSupOfRestrictToSubgroupMemSq.lean#L88-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemSupOfRestrictToSubgroupMemSq.lean#L88-L130

import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
import Definitions.Def_ReciprocityTheory_DualLattices_MemSupOfRestrictToSubgroupMemSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem ReciprocityTheory.PGsh.L2.mem_sup_of_restrictToSubgroup_mem_sq (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈
        augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by sorry
