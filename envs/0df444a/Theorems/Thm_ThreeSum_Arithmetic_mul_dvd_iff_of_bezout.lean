-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_mul_dvd_iff_of_bezout
-- name    : ThreeSum.Arithmetic.mul_dvd_iff_of_bezout
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:32:21.76989+00:00
-- url     : https://prove2.me/theorems/b874b50a-f9a8-4568-90c2-ce2b931d7384
-- title:
--   Product divisibility from a Bézout identity
-- statement:
--   Let $m,\ell,x\in\mathbb Z$. Suppose there are integers $u,v$ with $um+v\ell=1$. Then
--
--   $$m\ell\mid x\iff(m\mid x\ \land\ \ell\mid x).$$
--
--   The hypothesis is a concrete Bézout certificate; no positivity or primality assumption is required. The equivalence combines separate divisibility tests into one test for the product modulus.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Arithmetic.lean#L143-L165

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

theorem ThreeSum.Arithmetic.mul_dvd_iff_of_bezout : ∀ {m l x : Int}
  (hbez :
    ∃ (u : Int) (v : Int),
      @Eq.{1} Int
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) u m)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) v l))
        (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))),
  Iff (@Dvd.dvd.{0} Int Int.instDvd (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) m l) x)
    (And (@Dvd.dvd.{0} Int Int.instDvd m x) (@Dvd.dvd.{0} Int Int.instDvd l x)) := by
  sorry
