-- Prove2me | Theorems.Thm_ValuationSubring_valuation_intCast_eq_pow_pow_of_dvd
-- name    : ValuationSubring.valuation_intCast_eq_pow_pow_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/431d06e3-e827-556f-8e51-9402c1ad19c6
-- title:
--   Valuation of an integer as an ℓ-th power
-- statement:
--   Let $K$ be a field and $A \subseteq K$ a valuation subring, with associated valuation $v_A$ taking values in the value group of $A$ (a linearly ordered commutative group with zero). Let $q$ be a prime natural number whose image in $K$ satisfies $v_A(q) < 1$, so that $A$ lies over $q$ in the sense that $q$ is not a unit of $A$. Let $z$ be a nonzero integer and let $\ell$ be a natural number dividing the $q$-adic valuation $\operatorname{padicValInt} q\, z$ of $z$, i.e. the exponent of $q$ in $z$. The conclusion is the equality, in the value group of $A$, $$v_A(z) = \bigl(v_A(q)^{\,\operatorname{padicValInt} q\, z / \ell}\bigr)^{\ell},$$ where the exponent is the natural-number quotient (exact, by the divisibility hypothesis) and the cast of $z$ to $K$ is understood. In particular $v_A(z)$ is an $\ell$-th power in the value group; the statement records this in the explicit form exhibiting $v_A(q)^{\operatorname{padicValInt} q\, z/\ell}$ as an $\ell$-th root.
--
--   This is the arithmetic content of the numerical condition $\ell \mid v_q(\Delta)$ that appears in the analysis of a Tate curve at a prime $q$ of multiplicative reduction: it exhibits the valuation of the discriminant as an $\ell$-th power in the value group. It is used by [`WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd`](thm.html#WeierstrassCurve.smul_eq_self_of_torsion_of_not_inZeroComponentAt_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_intCast_eq_pow_pow_of_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_intCast_eq_pow_pow_of_dvd {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {z : ℤ} (hz : z ≠ 0) {ℓ : ℕ} (hℓ : ℓ ∣ padicValInt q z) :
    A.valuation (z : K) = (A.valuation (q : K) ^ (padicValInt q z / ℓ)) ^ ℓ := by sorry
