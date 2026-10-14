-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
-- name    : ThreeSum.SubsetAddress.layerRank_lt
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:43:07.490747+00:00
-- url     : https://prove2.me/theorems/e50e39f1-9ead-4eea-bec8-dc12db3f7f67
-- title:
--   A fixed-cardinality mask rank fits its binomial layer
-- statement:
--   Let $L,k,m\in\mathbb N$. Suppose $m<2^L$ and the binary mask $m$ has exactly $k$ selected positions among its $L$ positions. Let $\rho_{L,k}(m)$ be the construction's zero-based layer rank, defined by recursion on the highest available bit. Then
--
--   $$\rho_{L,k}(m)<\binom{L}{k}.$$
--
--   This guarantees that compact addresses for masks of a fixed cardinality stay inside the allocated binomial-size layer.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetAddress.lean#L118-L131

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.SubsetAddress.layerRank_lt : ∀ {L k m : Nat} (hm : ThreeSum.SubsetAddress.IsMask L k m),
  @LT.lt.{0} Nat instLTNat (ThreeSum.SubsetAddress.layerRank L k m) (L.choose k) := by
  sorry
