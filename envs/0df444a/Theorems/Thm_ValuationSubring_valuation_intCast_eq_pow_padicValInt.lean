-- Prove2me | Theorems.Thm_ValuationSubring_valuation_intCast_eq_pow_padicValInt
-- name    : ValuationSubring.valuation_intCast_eq_pow_padicValInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/291f620a-2de6-566f-9672-ed9af8a3c9aa
-- title:
--   Valuation of an integer in terms of v_A(q)
-- statement:
--   Let $K$ be a field and $A \subseteq K$ a valuation subring, with its canonical valuation $A.\mathrm{valuation} \colon K \to \Gamma_A$ taking values in the value group of $A$ (a linearly ordered commutative group with zero, written multiplicatively). Let $q$ be a prime natural number and assume that $q$ is in the maximal ideal in the sense that $A.\mathrm{valuation}(q) < 1$ in $\Gamma_A$; here $q$ is regarded as an element of $K$ via the canonical map. Let $z$ be a nonzero integer, viewed in $K$ by the canonical ring map. The conclusion is the equality
--   $$A.\mathrm{valuation}(z) \;=\; A.\mathrm{valuation}(q)^{\,\mathrm{padicValInt}\,q\,z}$$
--   in $\Gamma_A$, where $\mathrm{padicValInt}\,q\,z$ is the natural number $\mathrm{padicValNat}\,q\,|z|$, i.e. the exponent of $q$ in $|z|$, and the power is a power with natural exponent. Thus the restriction to $\mathbb{Z}$ of the valuation attached to $A$ is determined by its value on $q$ together with the $q$-adic valuation of the integer.
--
--   This is the integral row of the dictionary identifying the restriction to $\mathbb{Q}$ of a place lying over $q$ with the $q$-adic valuation, normalised multiplicatively. It is used for the corresponding statement about rational numbers ([`ValuationSubring.valuation_ratCast_eq_zpow_padicValRat`](thm.html#ValuationSubring.valuation_ratCast_eq_zpow_padicValRat)) and about prime powers dividing an integer ([`ValuationSubring.valuation_intCast_eq_pow_pow_of_dvd`](thm.html#ValuationSubring.valuation_intCast_eq_pow_pow_of_dvd)), and through these in the analysis of valuations of Weierstrass discriminants entering [`FreyPackage.frey_exists_inertia_not_fixed_at_two`](thm.html#FreyPackage.frey_exists_inertia_not_fixed_at_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_intCast_eq_pow_padicValInt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_intCast_eq_pow_padicValInt {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {z : ℤ} (hz : z ≠ 0) : A.valuation (z : K) = A.valuation (q : K) ^ padicValInt q z := by sorry
