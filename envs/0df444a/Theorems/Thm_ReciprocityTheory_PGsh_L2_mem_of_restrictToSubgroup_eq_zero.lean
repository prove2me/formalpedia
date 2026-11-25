-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_of_restrictToSubgroup_eq_zero
-- name    : ReciprocityTheory.PGsh.L2.mem_of_restrictToSubgroup_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:59.969035+00:00
-- url     : https://prove2.me/theorems/5e054ba4-8aba-4870-a2a4-db46c88f29d8
-- title:
--   L2: mem of restrict To Subgroup eq zero
-- statement:
--   The L2 construction uses the mem of restrict To Subgroup eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemSupOfRestrictToSubgroupMemSq.lean#L65-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemSupOfRestrictToSubgroupMemSq.lean#L65-L82

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

theorem ReciprocityTheory.PGsh.L2.mem_of_restrictToSubgroup_eq_zero (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by sorry
