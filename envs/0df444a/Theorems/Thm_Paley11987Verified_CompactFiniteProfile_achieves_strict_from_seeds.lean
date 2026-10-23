-- Prove2me | Theorems.Thm_Paley11987Verified_CompactFiniteProfile_achieves_strict_from_seeds
-- name    : Paley11987Verified.CompactFiniteProfile.achieves_strict_from_seeds
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-23T05:16:16.938639+00:00
-- url     : https://prove2.me/theorems/9b8d0681-ccda-4750-b106-cce303d32806
-- title:
--   An exponent from exponentially growing sensitivity witnesses
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Let $c,r,g,t$ be natural numbers greater than $1$, and let $\beta\ge0$ be real with
--   $$\beta<\frac{\log g}{\log r}.$$
--   Suppose that for every natural $m$ there is a Boolean function $f_m$ on finitely many coordinates satisfying
--   $$t^m\le s(f_m)\le cr^m,\qquad g^m\le bs(f_m).$$
--   Then every $\varepsilon>0$ and natural threshold $S\ge2$ admit a finite Boolean function $f$ with
--   $$s(f)\ge S,\qquad s(f)^{\beta-\varepsilon}\le bs(f).$$
--   This is the asymptotic passage from explicit finite seed bounds to an achieved campaign exponent.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfileAsymptotic, SHA256 f8d497dd3378991e1f80696f4cf2cf35e677b9a42f8b5703e02ee12e92ed0b5e; compact solution lines 10874-10919, compact SHA256 5f25b5da98678c1acd4e6a349cde81b6ba60c099acc44b634d4e7d985c4b5c20.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option Elab.async false

theorem Paley11987Verified.CompactFiniteProfile.achieves_strict_from_seeds :
∀ (c r g t : Nat) (β : Real),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) c →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) g →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) t →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β →
            @LT.lt.{0} Real Real.instLT β
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast g))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast r))) →
              (∀ (m : Nat),
                  @Exists.{1} Nat fun n =>
                    @Exists.{1} ((Fin n → Bool) → Bool) fun f =>
                      And
                        (@LE.le.{0} Nat instLENat
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) t
                            m)
                          (@OAI.Paper320.sensitivity (Fin n) (Fin.fintype n) f))
                        (And
                          (@LE.le.{0} Nat instLENat (@OAI.Paper320.sensitivity (Fin n) (Fin.fintype n) f)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                r m)))
                          (@LE.le.{0} Nat instLENat
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) g
                              m)
                            (@OAI.Paper320.blockSensitivity (Fin n) (Fin.fintype n) f)))) →
                SensitivityCampaign.AchievesExponent β := by sorry
