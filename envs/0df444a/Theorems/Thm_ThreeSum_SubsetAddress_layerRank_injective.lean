-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_layerRank_injective
-- name    : ThreeSum.SubsetAddress.layerRank_injective
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:50:10.75213+00:00
-- url     : https://prove2.me/theorems/e9d65553-a6b3-4fad-9324-0c2ccdaec891
-- title:
--   The rank within a fixed subset layer is injective
-- statement:
--   Let $L,k,m,n$ be natural numbers. Assume $m$ and $n$ encode subsets of $\{0,\ldots,L-1\}$ of cardinality $k$; equivalently, both integers are less than $2^L$ and have exactly $k$ set bits. Let $\rho_{L,k}$ denote the recursive rank within this fixed-cardinality layer, with masks lacking the highest bit placed before masks containing it. Then
--   $$\rho_{L,k}(m)=\rho_{L,k}(n)\quad\Longrightarrow\quad m=n.$$
--
--   Thus a layer rank uniquely identifies its valid subset mask, as required for compact subset addressing.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetAddress.lean#L133-L157

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.SubsetAddress.layerRank_injective : ∀ {L k m n : Nat} (hm : ThreeSum.SubsetAddress.IsMask L k m) (hn : ThreeSum.SubsetAddress.IsMask L k n)
  (he : @Eq.{1} Nat (ThreeSum.SubsetAddress.layerRank L k m) (ThreeSum.SubsetAddress.layerRank L k n)), @Eq.{1} Nat m n := by
  sorry
