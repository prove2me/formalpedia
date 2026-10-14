-- Prove2me | Theorems.Thm_ThreeSum_SubsetAddress_enumerateLayer_nodup
-- name    : ThreeSum.SubsetAddress.enumerateLayer_nodup
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:41:24.976219+00:00
-- url     : https://prove2.me/theorems/b8a29053-fea2-4f3e-84b4-9ba632287f44
-- title:
--   Fixed-weight bit-mask enumeration has no duplicates
-- statement:
--   For $L,k\in\mathbb N$, let $E_{L,k}$ be the recursively constructed list of $L$-bit masks having $k$ selected positions. The enumeration visits the lower half before the upper half and stops on empty layers. It has no repeated entries:
--
--   $$
--   \forall i,j<|E_{L,k}|,\qquad
--   E_{L,k}[i]=E_{L,k}[j]\Longrightarrow i=j.
--   $$
--
--   The assertion is uniform in $L$ and $k$: the zero-weight list contains only the zero mask, and layers with $k>L$ are empty.
--
--   This uniqueness property allows list positions to serve as unambiguous compact addresses for subsets of a fixed size.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/SubsetAddress.lean#L205-L220

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

theorem ThreeSum.SubsetAddress.enumerateLayer_nodup : ∀ (L k : Nat), @List.Nodup.{0} Nat (ThreeSum.SubsetAddress.enumerateLayer L k) := by
  sorry
