-- Prove2me | Theorems.Thm_WeierstrassCurve_hasseInvariant_jFamily
-- name    : WeierstrassCurve.hasseInvariant_jFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/23d7d574-6299-51df-8915-424efa631052
-- title:
--   Hasse invariant of the family y²+xy=x³-36tx-t
-- statement:
--   Let $q \ge 5$ be a prime and let $m, e_4, e_6$ be natural numbers with $12m + 4e_4 + 6e_6 = q-1$, $e_4 \le 2$ and $e_6 \le 1$. Let $k$ be an algebraically closed field of characteristic $q$, and let $S_0$ be a finite subset of $k$ whose elements are exactly the elements of $\mathrm{ssJSet}\ q\ k$, that is, those $j \in k$ such that every elliptic Weierstrass curve $W$ over $k$ with $j(W) = j$ has no point $P$ of its affine group with $q \cdot P = 0$ and $P \ne 0$. Consider the Weierstrass curve over the polynomial ring $k[X]$ with coefficients $a_1 = 1$, $a_2 = a_3 = 0$, $a_4 = -36X$, $a_6 = -X$, i.e. $y^2 + xy = x^3 - 36Xx - X$. Its Hasse invariant, defined as the coefficient of $x^{q-1}$ in the $\tfrac{q-1}{2}$-th power of the two-torsion cubic $4x^3 + b_2x^2 + 2b_4x + b_6$ and hence an element of $k[X]$, is asserted to equal
--   $$(1 + 1728X)^{2m + e_4 + e_6} \prod_{a \in S_0 \setminus \{0, 1728\}} \bigl(1 + (1728 - a)X\bigr).$$
--
--   For this family the parameter $X$ is $1/(j-1728)$, so the statement is the factorisation of the Hasse invariant of a universal family of $j$-lines into the linear factors attached to the supersingular $j$-invariants different from $0$ and $1728$, together with a power of $1 + 1728X$ accounting for the cuspidal fibre; it packages Deuring's criterion, the simplicity of the supersingular roots, and the degree and constant-term normalisation. It is used in the proof of [`ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one`](thm.html#ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one), which rewrites the identity in terms of the discriminant and the $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_hasseInvariant_jFamily.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_jFamily
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (m e₄ e₆ : ℕ) (hm : 12 * m + 4 * e₄ + 6 * e₆ = q - 1) (he₄ : e₄ ≤ 2) (he₆ : e₆ ≤ 1)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k)) =
      (1 + 1728 * Polynomial.X) ^ (2 * m + e₄ + e₆) *
        ∏ a ∈ S₀ \ {0, 1728}, (1 + Polynomial.C (1728 - a) * Polynomial.X) := by sorry
