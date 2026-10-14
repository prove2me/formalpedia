-- Prove2me | Theorems.Thm_ThreeSum_Cover_support_cauchy
-- name    : ThreeSum.Cover.support_cauchy
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:38:53.673464+00:00
-- url     : https://prove2.me/theorems/790921a1-7299-426b-8439-9da5f9c08eb2
-- title:
--   Cauchy–Schwarz using the actual support size
-- statement:
--   Let $\Omega$ be a finite type and $f:\Omega\to\mathbb R$. Define its support by $S=\{\omega\in\Omega:f(\omega)\ne0\}$. Then
--
--   $$
--   \left(\sum_{\omega\in\Omega}f(\omega)\right)^2\le |S|\sum_{\omega\in\Omega}f(\omega)^2.
--   $$
--
--   The estimate uses the number of nonzero entries rather than the size of the ambient set. It applies to arbitrary real values, including the zero function, and supports the moment estimates used in the cover analysis.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Cover.lean#L25-L47

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Cover.support_cauchy : ∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] (f : Ω → Real),
  @LE.le.{0} Real Real.instLE
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (∑ ω : Ω, f ω)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{u_1} Ω
          {ω : Ω | @Ne.{1} Real (f ω) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))}))
      (∑ ω : Ω,
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) (f ω)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  sorry
