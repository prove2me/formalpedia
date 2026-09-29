-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_prePsi_coeff_not_dvd_of_not_dvd_apOfModel
-- name    : WeierstrassCurve.exists_prePsi_coeff_not_dvd_of_not_dvd_apOfModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/89fc3056-5c5a-5280-97b6-744991a49a36
-- title:
--   Deuring's criterion in division-polynomial form at odd good primes
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$ and let $p$ be a natural number carrying the instance that it is prime, with $p \neq 2$. Assume two hypotheses: first, `W.IsGoodPrimeFor p`, which by the project's definition says only that the integer $p$ does not divide the discriminant $W.\Delta$; second, that $p$ does not divide the integer `W.apOfModel p`, where `apOfModel` is defined as the trace of Frobenius of the reduction `W.reductionMod p` obtained by mapping the coefficients of $W$ along $\mathbb{Z} \to \mathbb{Z}/p$, and where the trace of Frobenius of a curve over a commutative ring $F$ is defined as $\#F + 1 - N$ with $N$ the number of points of the associated affine curve, the point at infinity included. Under these hypotheses the conclusion asserts the existence of a natural number $i$ with $1 \le i$ and $i < (p^2 - 1)/2$ (natural subtraction and division) such that the integer $p$ does not divide the coefficient of $X^i$ in Mathlib's division polynomial `(W.preΨ' p)`, a polynomial over $\mathbb{Z}$. Equivalently: the reduction modulo $p$ of the $p$-th division polynomial of $W$ is not a constant, since for odd $p$ the coefficients of index $\ge (p^2-1)/2$ contribute only the leading term $p$. Nothing is asserted at $p = 2$, at primes dividing the discriminant, or in the converse direction.
--
--   Classically this is the division-polynomial shape of Deuring's description of $p$-torsion in characteristic $p$: at a good odd prime, $a_p$ being a $p$-unit (the ordinary case) forces the reduced $p$-division polynomial to have a root coming from a point of exact order $p$, hence to be non-constant. The formal statement is deliberately one-directional and phrased purely in terms of integral coefficients of `preΨ'` and of the project's `apOfModel`/`IsGoodPrimeFor`, with no reference to ordinarity, supersingularity or endomorphism rings. It is used downstream as the bridge between the $a_p$-currency and the division-polynomial currency of the ordinary condition: it feeds [`WeierstrassCurve.exists_torsionBy_integral_of_not_dvd_apOfModel_all_primes`](thm.html#WeierstrassCurve.exists_torsionBy_integral_of_not_dvd_apOfModel_all_primes) and, through that, the construction of deformation-ring data satisfying [`GaloisRep.ordinaryCondition`](def/GaloisRep_LocalConditions.html#L28) and the corresponding patching-datum statements at level $N$ exactly divisible by $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_prePsi_coeff_not_dvd_of_not_dvd_apOfModel.lean

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.exists_prePsi_coeff_not_dvd_of_not_dvd_apOfModel
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hgood : W.IsGoodPrimeFor p) (hap : ¬ (p : ℤ) ∣ W.apOfModel p) :
    ∃ i, 1 ≤ i ∧ i < (p ^ 2 - 1) / 2 ∧ ¬ (p : ℤ) ∣ (W.preΨ' p).coeff i := by sorry
