-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_four_relation_of_mask_ne
-- name    : ThreeSum.HashFamily.four_relation_of_mask_ne
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:47:45.049789+00:00
-- url     : https://prove2.me/theorems/2937a179-352e-4849-b675-b89872f4514b
-- title:
--   Different equality masks force independence of four one-hot words
-- statement:
--   Let $K$ be a ring and let $s,t,u,v:\alpha\to\{0,1\}$ be four pairwise distinct Boolean words. For a word $z$, define $e_z(i,b)=1$ if $z_i=b$ and zero otherwise. Suppose the equality masks of the pairs differ at some coordinate: $[s_i=t_i]\ne[u_i=v_i]$. If $a,b,c,d\in K$ satisfy
--
--   $$a e_s(p)+b e_t(p)+c e_u(p)+d e_v(p)=0\qquad\text{for every }p\in\alpha\times\{0,1\},$$
--
--   then
--
--   $$a=b=c=d=0.$$
--
--   This isolates the only possible four-endpoint dependence relevant to the hash moments: distinct equality masks cannot support a nontrivial relation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L70-L98

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_HashFamily_three_relation


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.HashFamily.four_relation_of_mask_ne : ∀ {α : Type u_1} {K : Type u_2} [inst : Ring.{u_2} K] {s t u v : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t)
  (hsu : @Ne.{u_1 + 1} (α → Bool) s u) (hsv : @Ne.{u_1 + 1} (α → Bool) s v) (htu : @Ne.{u_1 + 1} (α → Bool) t u)
  (htv : @Ne.{u_1 + 1} (α → Bool) t v) (huv : @Ne.{u_1 + 1} (α → Bool) u v)
  (hm :
    ∃ (i : α),
      @Ne.{1} Bool (@BEq.beq.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) (s i) (t i))
        (@BEq.beq.{0} Bool (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool) (u i) (v i)))
  {a b c d : K}
  (h :
    ∀ (p : Prod.{u_1, 0} α Bool),
      @Eq.{u_2 + 1} K
        (@HAdd.hAdd.{u_2, u_2, u_2} K K K
          (@instHAdd.{u_2} K (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
          (@HAdd.hAdd.{u_2, u_2, u_2} K K K
            (@instHAdd.{u_2} K
              (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
            (@HAdd.hAdd.{u_2, u_2, u_2} K K K
              (@instHAdd.{u_2} K
                (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
              (@HMul.hMul.{u_2, u_2, u_2} K K K
                (@instHMul.{u_2} K
                  (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                a
                (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                  (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                  (@AddMonoidWithOne.toOne.{u_2} K
                    (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                  s p))
              (@HMul.hMul.{u_2, u_2, u_2} K K K
                (@instHMul.{u_2} K
                  (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
                b
                (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                  (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                  (@AddMonoidWithOne.toOne.{u_2} K
                    (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                  t p)))
            (@HMul.hMul.{u_2, u_2, u_2} K K K
              (@instHMul.{u_2} K
                (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
              c
              (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                (@AddMonoidWithOne.toOne.{u_2} K
                  (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                u p)))
          (@HMul.hMul.{u_2, u_2, u_2} K K K
            (@instHMul.{u_2} K
              (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
            d
            (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
              (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
              (@AddMonoidWithOne.toOne.{u_2} K
                (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
              v p)))
        (@OfNat.ofNat.{u_2} K (nat_lit 0)
          (@Zero.toOfNat0.{u_2} K
            (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))))),
  And
    (@Eq.{u_2 + 1} K a
      (@OfNat.ofNat.{u_2} K (nat_lit 0)
        (@Zero.toOfNat0.{u_2} K
          (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
    (And
      (@Eq.{u_2 + 1} K b
        (@OfNat.ofNat.{u_2} K (nat_lit 0)
          (@Zero.toOfNat0.{u_2} K
            (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
      (And
        (@Eq.{u_2 + 1} K c
          (@OfNat.ofNat.{u_2} K (nat_lit 0)
            (@Zero.toOfNat0.{u_2} K
              (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
        (@Eq.{u_2 + 1} K d
          (@OfNat.ofNat.{u_2} K (nat_lit 0)
            (@Zero.toOfNat0.{u_2} K
              (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))))))) := by
  sorry
