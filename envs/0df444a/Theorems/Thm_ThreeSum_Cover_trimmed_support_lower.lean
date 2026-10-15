-- Prove2me | Theorems.Thm_ThreeSum_Cover_trimmed_support_lower
-- name    : ThreeSum.Cover.trimmed_support_lower
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:43:40.373197+00:00
-- url     : https://prove2.me/theorems/ca9a86f4-9826-4047-b4d2-a33379218df3
-- title:
--   A first- and second-moment bound forces large support
-- statement:
--   Let $\Omega$ be a nonempty finite set of size $N$, let $f:\Omega\to\mathbb R$, and let $\lambda>0$. Suppose
--
--   $$\frac{\lambda N}{2}\le\sum_{\omega\in\Omega}f(\omega),\qquad\sum_{\omega\in\Omega}f(\omega)^2\le5\lambda N.$$
--
--   Then
--
--   $$\lambda N\le20\,|\{\omega\in\Omega:f(\omega)\ne0\}|.$$
--
--   No pointwise nonnegativity assumption on $f$ is needed. This finite support estimate supplies the coverage frequency obtained from the trimmed hash moments.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Cover.lean#L49-L68

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Cover_support_cauchy


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Cover.trimmed_support_lower : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] [Nonempty.{u_1 + 1} Ω] (f : Ω → Real) {lam : Real}
  (hlam : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lam)
  (hfirst :
    @LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) lam
          (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} Ω inst)))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
      (∑ ω : Ω, f ω))
  (hsecond :
    @LE.le.{0} Real Real.instLE
      (∑ ω : Ω,
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (f ω)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          lam)
        (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} Ω inst)))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) lam
      (@Nat.cast.{0} Real Real.instNatCast (@Fintype.card.{u_1} Ω inst)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 20)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
      (@Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{u_1} Ω
          {ω : Ω | @Ne.{1} Real (f ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))}))) := by
  sorry
