-- Prove2me | Theorems.Thm_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul
-- name    : PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/4f5966d3-3776-5408-b6d9-30bf249cfd65
-- title:
--   Lattice multipliers give rational homomorphisms of Weierstrass curves
-- statement:
--   Let $L$ and $L'$ be period pairs, with associated lattices `L.lattice`, `L'.lattice` and associated Weierstrass curves over $\mathbb{C}$, namely $y^2 = x^3 - (g_2/4)x - (g_3/4)$ with the invariants of the respective pair; let $hL$, $hL'$ be the hypotheses that the quantities $g_2^3 - 27 g_3^2$ of $L$ and of $L'$ are non-zero (these in fact always hold, by [`PeriodPair.discriminant_ne_zero`](thm.html#PeriodPair.discriminant_ne_zero)), so that the Weierstrass parametrisations $L.\mathtt{toPoint}\ hL$ and $L'.\mathtt{toPoint}\ hL'$ are defined: each sends a lattice point to the point at infinity and any other $z$ to the affine point whose coordinates are the values at $z$ of the Weierstrass functions of the pair, nonsingular because the discriminant does not vanish. Let $a \in \mathbb{C}$ be such that $a l \in L'.\mathtt{lattice}$ for every $l \in L.\mathtt{lattice}$. Then there exists an additive map $\beta$ from the points of the first curve to the points of the second, lying in [`WeierstrassCurve.rationalHomSet ℂ`](def/WeierstrassCurve_RationalEnd.html#L28), i.e. either $\beta = 0$ or there are bivariate polynomials $n_X, d_X, n_Y, d_Y$ over $\mathbb{C}$ and a finite set $B$ of abscissae outside which $\beta$ sends every nonsingular affine point $(x,y)$ to $(n_X/d_X, n_Y/d_Y)$ evaluated at $(x,y)$, with both denominators non-vanishing there, such that $\beta(L.\mathtt{toPoint}\ hL\ z) = L'.\mathtt{toPoint}\ hL'\ (a z)$ for every $z \in \mathbb{C}$. No uniqueness of $\beta$, and no non-vanishing of $\beta$, is asserted.
--
--   This is the surjectivity half of the classical dictionary between complex numbers $a$ with $a\Lambda \subseteq \Lambda'$ and homomorphisms $E_\Lambda \to E_{\Lambda'}$: multiplication by such an $a$ descends through the Weierstrass parametrisations to an algebraic homomorphism of the corresponding Weierstrass curves. It feeds the construction of non-zero rational endomorphisms from analytic data in [`WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul`](thm.html#WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (a : ℂ) (ha : ∀ l ∈ L.lattice, a * l ∈ L'.lattice) : ∃ β ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve, ∀ z : ℂ, β (L.toPoint hL z) = L'.toPoint hL' (a * z) := by sorry
