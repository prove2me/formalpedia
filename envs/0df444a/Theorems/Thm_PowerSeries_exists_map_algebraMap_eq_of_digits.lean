-- Prove2me | Theorems.Thm_PowerSeries_exists_map_algebraMap_eq_of_digits
-- name    : PowerSeries.exists_map_algebraMap_eq_of_digits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/291c9df7-4c6c-5b75-9d11-0ef4c095ec63
-- title:
--   Integrality of power-series expansions from t-adic digits
-- statement:
--   Let $R$, $R'$ and $L$ be commutative rings with $L$ an $R$-algebra, let $\iota : R \to R'$ be a ring homomorphism, $I \subseteq R'$ an ideal, $t \in R'$ an element, and let $e : R' \to L[[q]]$ be a ring homomorphism into the power series ring over $L$. Assume: (i) for every $r \in R$, $e(\iota r)$ is the constant series with value $\mathrm{algebraMap}_{R,L}(r)$; (ii) for every $i \in I$, the constant coefficient of $e(i)$ vanishes; (iii) there is $u \in R[[q]]$ with $e(t)$ equal to the coefficientwise image of $u$ under $\mathrm{algebraMap}_{R,L}$; and (iv) every element of $R'$ admits $t$-adic digits in $R$ along $I$, i.e. for every $z \in R'$ and every $n \in \mathbb{N}$ there is a sequence $a : \mathbb{N} \to R$ with $z - \sum_{i < n} \iota(a_i)\, t^i \in I^n$. Then for every $z \in R'$ there exists $P \in R[[q]]$ whose coefficientwise image under $\mathrm{algebraMap}_{R,L}$ equals $e(z)$. Thus $e$ takes values in the image of $R[[q]]$ in $L[[q]]$.
--
--   This is the series-side step of the integral $q$-expansion principle: a formal expansion map whose values are known to be integral on one parameter $t$, and which kills constant terms along $I$, is integral on the whole ring, provided elements of $R'$ have $t$-adic digit expansions modulo powers of $I$. It is used by [`RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq`](thm.html#RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_map_algebraMap_eq_of_digits.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PowerSeries.exists_map_algebraMap_eq_of_digits
    {R R' L : Type*} [CommRing R] [CommRing R'] [CommRing L] [Algebra R L]
    (ι : R →+* R') (I : Ideal R') (t : R') (e : R' →+* PowerSeries L)
    (hι : ∀ r : R, e (ι r) = PowerSeries.C (algebraMap R L r))
    (hI : ∀ i ∈ I, PowerSeries.constantCoeff (e i) = 0)
    (u : PowerSeries R) (ht : e t = u.map (algebraMap R L))
    (hdig : ∀ (z : R') (n : ℕ), ∃ a : ℕ → R, z - ∑ i ∈ Finset.range n, ι (a i) * t ^ i ∈ I ^ n)
    (z : R') : ∃ P : PowerSeries R, e z = P.map (algebraMap R L) := by sorry
