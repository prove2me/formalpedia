-- Prove2me | Theorems.Thm_ThreeSum_Parameters_phi_le_gamma
-- name    : ThreeSum.Parameters.phi_le_gamma
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:13.223151+00:00
-- url     : https://prove2.me/theorems/f387fe06-e32e-4d8b-84d7-bc9dd6b4190c
-- title:
--   The cubic switch polynomial bounds entropy loss from below
-- statement:
--   Let $H_2$ be binary entropy in bits and set
--   $\phi(t)=\frac{799}{100}t+\frac{18}{25}t^2+\frac6{25}t^3$.
--   The loss in the output-support entropy when its fraction is reduced by $t$ is
--   $\gamma(t)=256H_2(1/256)-256H_2((1-t)/256)$.
--   For every real $t\in[0,1/2]$,
--
--   $$
--   \phi(t)\le\gamma(t).
--   $$
--
--   All polynomial coefficients are exact rationals, and the interval is closed.
--
--   This validates the polynomial surrogate used by the integer cubic-switch test: a certified polynomial threshold also gives the required entropy-loss threshold at every permitted switch fraction.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Parameters.lean#L426-L446

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

theorem ThreeSum.Parameters.phi_le_gamma : ∀ {t : Real}
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
  @LE.le.{0} Real Real.instLE (ThreeSum.Parameters.phi t) (ThreeSum.Parameters.gamma t) := by
  sorry
