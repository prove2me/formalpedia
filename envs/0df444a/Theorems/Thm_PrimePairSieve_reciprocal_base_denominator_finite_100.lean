-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_finite_100
-- name    : PrimePairSieve.reciprocal_base_denominator_finite_100
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T16:35:16.725437+00:00
-- url     : https://prove2.me/theorems/78b84c6b-cb60-462c-b503-c874f4d1b9e3
-- title:
--   Reciprocal sieve threshold on the real interval [40,100]
-- statement:
--   Let $C$ be the mission's twin-prime constant and define $w(n)=0$ for nonsquarefree $n$. For squarefree $n$, let $w(n)$ be the product over its prime factors of $1$ at $p=2$ and $2/(p-2)$ otherwise. For every real $40\le z\le 100$,
--
--   $$\frac{\log^2(4z)}{2C}\left(1-\frac{(z+1)\log^2(4z)}{32Cz^2}\right)^{-1}\le\sum_{1\le n\le\lfloor z\rfloor}\frac{w(n)}{1+n/z}.$$
--
--   This certifies a bounded portion of the existing reciprocal sieve threshold, retaining its real variable, natural floor and literal squarefree normalization. It is one component of the finite-window alternative to the sharp remainder estimate; it does not assert the whole range through two million or the mission root.
-- source:
--   Exact bounded restriction of PrimePairSieve.reciprocal_base_denominator_dominates_threshold, https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; generated certificate applying accepted interval criterion 399f4fad-953d-4b94-880a-84fb162caaa7.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semifield
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_base_denominator_finite_100 (z : ℝ) (hz : 40 ≤ z) (hupper : z ≤ 100) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree n then ∏ p ∈ n.primeFactors, if p = 2 then (1:ℝ) else 2/((p:ℝ)-2) else 0)/(1+(n:ℝ)/z) := by sorry
