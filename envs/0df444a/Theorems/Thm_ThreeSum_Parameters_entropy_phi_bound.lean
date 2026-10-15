-- Prove2me | Theorems.Thm_ThreeSum_Parameters_entropy_phi_bound
-- name    : ThreeSum.Parameters.entropy_phi_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:05.141278+00:00
-- url     : https://prove2.me/theorems/d20a9e2b-1ac4-4ce6-8cd5-ea5d8654c6a2
-- title:
--   A uniform entropy bound by the cubic switch polynomial
-- statement:
--   Let $H_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ be binary entropy, using the continuous endpoint convention $0\log_20=0$. Define the rational polynomial
--   $\phi(t)=\frac{799}{100}t+\frac{18}{25}t^2+\frac6{25}t^3$. For every real $t\in[0,1/2]$,
--
--   $$
--   H_2(t)<\frac{277}{1000}\bigl(1+\phi(t)\bigr).
--   $$
--
--   The inequality is strict throughout the closed interval, including both endpoints, and all displayed coefficients are exact rationals.
--
--   This is the analytic comparison used to control query-layer entropy by the polynomial switch criterion in the exponent calculation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Parameters.lean#L321-L339

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Parameters.entropy_phi_bound : ∀ {t : Real}
  (ht :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
      t),
  @LT.lt.{0} Real Real.instLT (ThreeSum.Parameters.entropy t)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ThreeSum.Parameters.entropyRatio
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (ThreeSum.Parameters.phi t))) := by
  sorry
