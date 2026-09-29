-- Prove2me | Theorems.Thm_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
-- name    : ValuationRing.exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/0e24d2cc-382d-5246-8542-7c826caf1e01
-- title:
--   Tame action on a rank-one F_q-vector space scheme, e=1
-- statement:
--   Let $R$ be a commutative ring and $p$ a natural number whose image in $R$ is irreducible. Let $S$ be an $R$-algebra which is an integral domain and a valuation ring, such that the image of $p$ in $S$ is nonzero and lies in the maximal ideal of the local ring $S$. Let $\sigma : S \to S$ be an $R$-algebra endomorphism with $\sigma(y) - y$ in the maximal ideal for every $y \in S$. Let $r \geq 1$, let $\delta : \mathrm{Fin}\, r \to R$ with $\delta_i \mid p$ for each $i$, let $x : \mathrm{Fin}\, r \to S$ satisfy $x_i^{\,p} = \delta_i\, x_{i+1}$ for all $i$ (indices taken cyclically in $\mathrm{Fin}\, r$), and let $\pi' \in S$ satisfy $\pi'^{\,p^r - 1} = p$ in $S$. The conclusion asserts the existence of exponents $n : \mathrm{Fin}\, r \to \mathbb{N}$ with $n_i \leq 1$ and $\delta_i$ associated in $R$ to $p^{n_i}$ for every $i$, together with an element $t \in S$ with $t^{p^r - 1} = 1$, $\sigma(\pi') = t\,\pi'$, and $\sigma(x_i) = t^{\,e_i} x_i$ for every $i$, where $e_i = \sum_{j \in \mathrm{Fin}\, r} n_{i+j}\, p^{\,r - 1 - j}$, the integer whose base-$p$ digits from the top are $n_i, n_{i+1}, \dots, n_{i+r-1}$.
--
--   This is Raynaud's computation of the action of inertia on the points of a rank-one $\mathbf{F}_q$-vector space scheme, given by equations $X_i^p = \delta_i X_{i+1}$, in the case of absolute ramification index one, where the digits $n_i$ are $0$ or $1$ and the action is through the fundamental character of level $r$ raised to the exponent with those digits; over a valuation ring no henselian hypothesis is needed. It is used in the step extracting an additive eigenfunctional with tame character for finite flat group schemes with simple inertia action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationRing_exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul.lean

import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem ValuationRing.exists_algHom_apply_eq_pow_digitSum_mul_of_forall_pow_eq_mul
    {R : Type u} [CommRing R] {p : ℕ} (hunif : Irreducible (p : R))
    {S : Type v} [CommRing S] [IsDomain S] [ValuationRing S] [Algebra R S]
    (hpS : algebraMap R S p ∈ IsLocalRing.maximalIdeal S) (hp0 : algebraMap R S p ≠ 0)
    (σ : S →ₐ[R] S) (hσ : ∀ y : S, σ y - y ∈ IsLocalRing.maximalIdeal S)
    {r : ℕ} [NeZero r] (δ : Fin r → R) (hδ : ∀ i, δ i ∣ (p : R))
    (x : Fin r → S) (hx : ∀ i, x i ^ p = algebraMap R S (δ i) * x (i + 1))
    (π' : S) (hπ' : π' ^ (p ^ r - 1) = algebraMap R S p) :
    ∃ n : Fin r → ℕ, (∀ i, n i ≤ 1) ∧ (∀ i, Associated (δ i) ((p : R) ^ n i)) ∧
      ∃ t : S, t ^ (p ^ r - 1) = 1 ∧ σ π' = t * π' ∧
        ∀ i, σ (x i) = t ^ (∑ j : Fin r, n (i + j) * p ^ (r - 1 - (j : ℕ))) * x i := by sorry
