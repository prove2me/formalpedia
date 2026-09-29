-- Prove2me | Theorems.Thm_Polynomial_Monic_map_roots_eq_of_map_eq_kroneckerFibre
-- name    : Polynomial.Monic.map_roots_eq_of_map_eq_kroneckerFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/7448e99a-dfb4-5a84-bdf0-82d5712c1e45
-- title:
--   Reduced roots of a monic lift of (a^q-X)(a-X^q)
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring of $L$, let $k$ be a field, and let $q$ be a natural number assumed prime with $k$ of characteristic $q$. Let $\mathrm{red} \colon A \to k$ be a ring homomorphism and let $r \colon L \to k$ be any function (not assumed to be a homomorphism) agreeing with $\mathrm{red}$ on $A$, i.e. $r(a) = \mathrm{red}(a)$ for every $a \in A$. Let $P \in A[X]$ be monic, let $a, b \in k$ satisfy $b^q = a$, and assume that the coefficientwise reduction of $P$ along $\mathrm{red}$ is the polynomial $(C(a^q) - X)\,(C(a) - X^q) \in k[X]$. The conclusion is an identity of multisets in $k$: the multiset of roots of $P$ viewed in $L[X]$ (via the inclusion $A \to L$), counted with multiplicity, has pushforward under $r$ equal to $\{a^q\} + q \cdot \{b\}$, the multiset consisting of $a^q$ once together with $q$ copies of $b$. In particular the root multiset of $P$ in $L$ has cardinality $q+1$, one root reducing to $a^q$ and $q$ roots reducing to $b$.
--
--   This is the root-specialisation step for a monic integral lift of the Kronecker fibre polynomial: it converts the characteristic-$q$ factorisation $(a^q - X)(a - X^q)$, in which the second factor is a $q$-th power by Frobenius, into a count, with multiplicity, of how the $q+1$ geometric roots in $L$ distribute between the two branches after reduction. It is used in the construction of places specialising the relevant Hecke divisor on the modular curve $X_1$, in the statement [`ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_single_add_sum_and_apply_jChartFin_eq_pow_of_apply_eq_pow_of_spec_comp_iotaFin_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_Monic_map_roots_eq_of_map_eq_kroneckerFibre.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.Monic.map_roots_eq_of_map_eq_kroneckerFibre
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (red : A →+* k) (r : L → k) (hr : ∀ a : A, r a = red a)
    {P : Polynomial A} (hP : P.Monic) (a b : k) (hb : b ^ q = a)
    (hred : P.map red = (Polynomial.C (a ^ q) - Polynomial.X) * (Polynomial.C a - Polynomial.X ^ q)) :
    ((P.map (algebraMap A L)).roots).map r = {a ^ q} + q • ({b} : Multiset k) := by sorry
