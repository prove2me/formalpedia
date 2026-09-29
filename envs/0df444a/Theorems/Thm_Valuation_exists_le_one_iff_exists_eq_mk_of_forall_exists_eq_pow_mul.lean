-- Prove2me | Theorems.Thm_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
-- name    : Valuation.exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/9e354c91-203a-50f4-9656-90fa607934f9
-- title:
--   A discrete valuation from factorisation by a parameter t
-- statement:
--   Let $M$ be a commutative ring which is a domain, $K$ a field, $\varphi : M \to K$ a ring homomorphism, and $t \in M$ with $t \neq 0$ and $\varphi(t) = 0$; assume that every nonzero $F \in M$ admits a factorisation $F = t^{n} G$ with $n \in \mathbb{N}$, $G \in M$ and $\varphi(G) \neq 0$. Then there exists a valuation $v$ on the fraction field $\operatorname{Frac} M$ with values in $\mathbb{Z}^{m0}$ (the integers written multiplicatively with a zero adjoined) such that: (i) for every $x \in \operatorname{Frac} M$, one has $v(x) \le 1$ if and only if $x$ can be written as the fraction $a/b$ with $a, b \in M$, $b$ a non-zero-divisor and $\varphi(b) \neq 0$; (ii) for all such $a$, $b$ with $b$ a non-zero-divisor and $\varphi(b) \neq 0$, one has $v(a/b) < 1$ if and only if $\varphi(a) = 0$; (iii) $v$ of the image of $t$ in $\operatorname{Frac} M$ equals $\exp(-1)$, the element of $\mathbb{Z}^{m0}$ corresponding to the integer $-1$; and (iv) there is a ring homomorphism $\psi$ from the valuation subring of $v$ to $K$ satisfying $\psi(x) = \varphi(a)/\varphi(b)$ for every element $x$ of that subring and every presentation $x = a/b$ with $b$ a non-zero-divisor and $\varphi(b) \neq 0$.
--
--   This is the standard construction of a normalised discrete valuation from a parameter: the order of vanishing in $t$ defines $v$, the valuation ring is the set of fractions with denominator of non-zero image under $\varphi$, and the residue map is induced by $\varphi$. It is a statement of pure commutative algebra, used in the construction of places on the Mumford-type fields attached to points of Drinfeld's upper half plane, via [`CerednikDrinfeld.Omega.exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving`](thm.html#CerednikDrinfeld.Omega.exists_place_invariantFieldOf_mem_iff_and_evalAt_eq_div_of_map_le_typePreserving).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul.lean

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WithZero

theorem Valuation.exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul
    (M : Type) [CommRing M] [IsDomain M] (K : Type) [Field K] (φ : M →+* K) (t : M) (ht0 : t ≠ 0) (ht : φ t = 0)
    (hfac : ∀ F : M, F ≠ 0 → ∃ (n : ℕ) (G : M), F = t ^ n * G ∧ φ G ≠ 0) :
    ∃ v : Valuation (FractionRing M) ℤᵐ⁰,
      (∀ x : FractionRing M, v x ≤ 1 ↔
        ∃ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 ∧ x = Localization.mk a ⟨b, hb⟩) ∧
      (∀ (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 →
        (v (Localization.mk a ⟨b, hb⟩ : FractionRing M) < 1 ↔ φ a = 0)) ∧
      v (algebraMap M (FractionRing M) t) = exp (-1) ∧
      ∃ ψ : ↥v.valuationSubring →+* K, ∀ (x : ↥v.valuationSubring) (a b : M) (hb : b ∈ nonZeroDivisors M), φ b ≠ 0 →
        (x : FractionRing M) = Localization.mk a ⟨b, hb⟩ → ψ x = φ a / φ b := by sorry
