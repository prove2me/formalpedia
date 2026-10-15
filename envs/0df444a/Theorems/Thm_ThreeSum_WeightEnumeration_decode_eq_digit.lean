-- Prove2me | Theorems.Thm_ThreeSum_WeightEnumeration_decode_eq_digit
-- name    : ThreeSum.WeightEnumeration.decode_eq_digit
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:44:20.464974+00:00
-- url     : https://prove2.me/theorems/c7404bb2-f9e2-4966-a224-02983fdb8ea5
-- title:
--   A decoded coordinate is the digit at its first occurrence
-- statement:
--   Let $\iota$ have decidable equality and let $K$ have a specified cast $c:\mathbb N\to K$. Let $l$ be a list of indices, $i\in l$, and let $t$ be the zero-based first-occurrence index of $i$ in $l$. For any natural radix $p$ and natural input $k$, the recursive decoder satisfies
--
--   $$D_{p,l}(k)(i)=c\!\left(\operatorname{mod}_{\mathbb N}\!\left(\operatorname{div}_{\mathbb N}(k,p^{|l|-1-t}),p\right)\right).$$
--
--   Natural division and remainder use their total conventions, so radix zero is included; no upper bound on $k$ is assumed. This formula connects dependent coordinate assignments to direct digit extraction even when labels repeat.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WeightEnumeration.lean#L66-L81

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

universe u_1 u_2

theorem ThreeSum.WeightEnumeration.decode_eq_digit : ∀ {ι : Type u_1} {K : Type u_2} [inst : DecidableEq.{u_1 + 1} ι] [inst_1 : NatCast.{u_2} K] (p : Nat) (l : List.{u_1} ι)
  (k : Nat) (i : ι) (hi : @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i),
  @Eq.{u_2 + 1} K (@ThreeSum.WeightEnumeration.decode.{u_1, u_2} ι K inst inst_1 p l k i hi)
    (@Nat.cast.{u_2} K inst_1
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) k
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@List.length.{u_1} ι l)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@List.idxOf.{u_1} ι (@instBEqOfDecidableEq.{u_1} ι inst) i l))))
        p)) := by
  sorry
