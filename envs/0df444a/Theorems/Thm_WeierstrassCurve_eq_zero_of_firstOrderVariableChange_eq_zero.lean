-- Prove2me | Theorems.Thm_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero
-- name    : WeierstrassCurve.eq_zero_of_firstOrderVariableChange_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/14f9df0e-8a27-5c3e-84d5-745aa6688eb1
-- title:
--   No first-order automorphisms of an elliptic Weierstrass curve
-- statement:
--   Let $R$ be a commutative ring and let $E$ be a Weierstrass curve over $R$, given by coefficients $a_1,a_2,a_3,a_4,a_6 \in R$ (written `E.a₁`, …, `E.a₆`), which is assumed elliptic in the sense of Mathlib's `WeierstrassCurve.IsElliptic`, i.e. its discriminant $\Delta$ is a unit of $R$. Let $\mu,\rho,\varsigma,\tau \in R$ satisfy the five linear relations $a_1\mu + 2\varsigma = 0$, $2a_2\mu + 3\rho - a_1\varsigma = 0$, $3a_3\mu + a_1\rho + 2\tau = 0$, $4a_4\mu + 2a_2\rho - a_3\varsigma - a_1\tau = 0$ and $6a_6\mu + a_4\rho - a_3\tau = 0$. Then $\mu = 0$, $\rho = 0$, $\varsigma = 0$ and $\tau = 0$. No assumption is made on the characteristic of $R$ or on the invertibility of $2$ or $3$; the hypotheses are exactly the vanishing of the five coordinates of the displacement of $(a_1,a_2,a_3,a_4,a_6)$ under an infinitesimal admissible change of variables with parameters $(\mu,\rho,\varsigma,\tau)$, and the conclusion asserts that such a displacement vanishes only for the trivial parameters.
--
--   This is the infinitesimal rigidity of the admissible-change-of-variables action on elliptic Weierstrass equations: the tangent map at the identity of $(u,r,s,t) \mapsto (u,r,s,t) \cdot E$ is injective over any commutative ring in which the discriminant is invertible, which is the algebraic form of the statement that automorphisms of elliptic curves are unramified. It is used in the lifting results for Weierstrass curves over rings with a square-zero maximal ideal, such as [`WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot) and [`WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot`](thm.html#WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot), where it supplies the uniqueness half of the deformation argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.eq_zero_of_firstOrderVariableChange_eq_zero
    (R : Type) [CommRing R] (E : WeierstrassCurve R) [E.IsElliptic] (μ ρ ς τ : R)
    (h₁ : E.a₁ * μ + 2 * ς = 0)
    (h₂ : 2 * E.a₂ * μ + 3 * ρ - E.a₁ * ς = 0)
    (h₃ : 3 * E.a₃ * μ + E.a₁ * ρ + 2 * τ = 0)
    (h₄ : 4 * E.a₄ * μ + 2 * E.a₂ * ρ - E.a₃ * ς - E.a₁ * τ = 0)
    (h₆ : 6 * E.a₆ * μ + E.a₄ * ρ - E.a₃ * τ = 0) :
    μ = 0 ∧ ρ = 0 ∧ ς = 0 ∧ τ = 0 := by sorry
