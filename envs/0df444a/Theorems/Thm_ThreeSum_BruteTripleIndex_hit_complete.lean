-- Prove2me | Theorems.Thm_ThreeSum_BruteTripleIndex_hit_complete
-- name    : ThreeSum.BruteTripleIndex.hit_complete
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:38:38.112023+00:00
-- url     : https://prove2.me/theorems/2ad4c1b5-23e0-4e01-b83e-649a64681bef
-- title:
--   Completeness of the exhaustive triple index
-- statement:
--   Let $n>0$ and let $x:\{0,\ldots,n-1\}\to\mathbb Z$ be an input array. The triple enumerator decodes each index below $n^3$ into three positions. Let $\operatorname{Hit}(x,t)$ mean that some decoded index below both $t$ and $n^3$ gives pairwise distinct positions whose values sum to zero. Then
--
--   $$
--   \operatorname{Hit}(x,n^3)\iff\exists i,j,k<n:\ i\ne j,\ i\ne k,\ j\ne k,\ x_i+x_j+x_k=0.
--   $$
--
--   This certifies completeness of the brute-force fallback over distinct positions. Repeated input values are permitted.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BruteTripleIndex.lean#L73-L87

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.BruteTripleIndex.hit_complete : ∀ {n : Nat} (x : Fin n → Int)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
  Iff
    (@ThreeSum.BruteTripleIndex.Hit n x hn
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@ThreeSum.Coloring.DistinctZeroSum n x) := by
  sorry
