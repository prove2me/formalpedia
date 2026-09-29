-- Prove2me | Theorems.Thm_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime
-- name    : Polynomial.irreducible_X_pow_sub_C_of_monoidHom_units_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/f15b572c-49d3-587a-b3ec-36eb2942bc17
-- title:
--   Irreducibility of X^N-β via a valuation-like homomorphism
-- statement:
--   Let $K$ be a field, let $N$ be a natural number with $0 < N$, and let $\beta \in K$ be nonzero. Let $\varphi \colon K^{\times} \to \mathrm{Multiplicative}\ \mathbb{Z}$ be a monoid homomorphism from the group of units of $K$ to the integers written multiplicatively, i.e. a group homomorphism $K^{\times} \to \mathbb{Z}$. Write $\beta$ for the unit `Units.mk0 β hβ` determined by $\beta$ and its nonvanishing, and let $\varphi(\beta) \in \mathbb{Z}$ denote the image of $\varphi$ at that unit read additively via `Multiplicative.toAdd`. Assume that the absolute value $|\varphi(\beta)|$, as a natural number, is coprime to $N$. Then the polynomial $X^{N} - C\,\beta$ is irreducible in $K[X]$. No hypothesis is made on the characteristic of $K$, on the parity of $N$, or on the presence of roots of unity in $K$; the coprimality of $|\varphi(\beta)|$ with $N$ carries the whole burden.
--
--   This is the classical Capelli-type criterion for the irreducibility of $X^{N} - \beta$ in the form most convenient for function fields: if some homomorphism $K^{\times} \to \mathbb{Z}$ (for instance the order of vanishing at a place) takes a value at $\beta$ prime to $N$, the binomial is irreducible. It is applied in the Kummer-theoretic description of Igusa curves, where the Hasse invariant has a zero of order prime to the relevant exponent, via [`ModularCurve.isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C`](thm.html#ModularCurve.isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem Polynomial.irreducible_X_pow_sub_C_of_monoidHom_units_coprime
    {K : Type u} [Field K] {N : ℕ} (hN : 0 < N) {β : K} (hβ : β ≠ 0)
    (φ : Kˣ →* Multiplicative ℤ)
    (hφ : (Multiplicative.toAdd (φ (Units.mk0 β hβ))).natAbs.Coprime N) :
    Irreducible (X ^ N - C β) := by sorry
