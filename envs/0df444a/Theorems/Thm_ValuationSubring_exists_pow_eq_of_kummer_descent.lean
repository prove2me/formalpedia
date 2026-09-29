-- Prove2me | Theorems.Thm_ValuationSubring_exists_pow_eq_of_kummer_descent
-- name    : ValuationSubring.exists_pow_eq_of_kummer_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/e832519f-5bb0-5d56-bdcd-58f53699b8f9
-- title:
--   Kummer descent at a Galois-stable place
-- statement:
--   Let $K \subseteq L$ be fields with $L$ algebraically closed of characteristic zero and $L/K$ Galois, and let $P$ be a valuation subring of $L$ that is stable under the action of the Galois group, in the sense that $\sigma x \in P$ for every $K$-algebra automorphism $\sigma$ of $L$ and every $x \in P$. Let $p$ and $q$ be distinct primes, and assume: the image of $q$ in $P$ lies in the maximal ideal of $P$ (so $P$ has residue characteristic $q$); every element of $L$ is algebraic over $\mathbb{Q}$; for every $k \in \mathbb{N}$ there is $r \in K$ with $r^{p^k} = q$ in $K$, i.e. $K$ contains a $p^k$-th root of $q$ for all $k$; and the valuation subring $P \cap K$ of $K$, obtained as the preimage of $P$ under the structure map $K \to L$, admits approximate $p$-th roots of units, in the sense that for every unit $u$ of $P \cap K$ there is $z \in P \cap K$ with $z^p - u$ in the maximal ideal of $P \cap K$. Then for every $a \in K$ with $a \neq 0$ there exists $b \in K$ with $b^p = a$.
--
--   This is a Kummer-descent statement: under the stated hypotheses on a Galois-stable place of $L$ with residue characteristic $q \neq p$, the base field $K$ is closed under extraction of $p$-th roots. It is used in the analysis of inertia subgroups attached to such places, namely in [`ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq) and its Galois variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_pow_eq_of_kummer_descent.lean

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Algebra.Rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_pow_eq_of_kummer_descent
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] [IsGalois K L] [CharZero L]
    (P : ValuationSubring L) (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P)
    (p q : ℕ) (hp : p.Prime) (hqp : q.Prime) (hpq : p ≠ q)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P)
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = (q : K))
    (hres : ∀ u : P.comap (algebraMap K L), IsUnit u →
      ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)))
    (a : K) (ha : a ≠ 0) : ∃ b : K, b ^ p = a := by sorry
