-- Prove2me | Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
-- name    : PeriodPair.exists_variableChange_smul_weierstrassCurve_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/8a943e5f-0e08-51be-ac4b-8a8bf8cc3a81
-- title:
--   Every complex elliptic curve is a lattice curve
-- statement:
--   Let $E$ be a Weierstrass curve over $\mathbb{C}$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, and assume $E$ is elliptic in Mathlib's sense, i.e. its discriminant is a unit of $\mathbb{C}$. The assertion is that there exist a period pair $L$ (a `PeriodPair`, with associated invariants $L.g_2$ and $L.g_3$) and an admissible change of Weierstrass coordinates $C$ over $\mathbb{C}$, that is an element $(u,r,s,t)$ with $u \in \mathbb{C}^\times$, such that the image of the Weierstrass curve attached to $L$ under $C$ is exactly $E$. Here the curve attached to $L$ is the one with $a_1 = a_2 = a_3 = 0$, $a_4 = -L.g_2/4$ and $a_6 = -L.g_3/4$, that is $y^2 = x^3 - \tfrac{1}{4}g_2(L)\,x - \tfrac{1}{4}g_3(L)$, and the equality $C \bullet L.\mathrm{weierstrassCurve} = E$ is equality of Weierstrass curves, i.e. of all five coefficients, not merely an isomorphism of the associated curves.
--
--   This is the algebraic half of the uniformisation theorem over $\mathbb{C}$: every elliptic curve in Weierstrass form arises, after an admissible coordinate change, from the Eisenstein invariants of a lattice. It is used in the project's work with complex-analytic models of elliptic curves, in particular in the results on isogeny data, modular polynomials and rational homomorphism sets that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean

import Mathlib
import Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := by sorry
