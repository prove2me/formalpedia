-- Prove2me | Theorems.Thm_QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange
-- name    : QuotientGroup.eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/620f84e0-cdd6-52e8-9ecf-33682329e562
-- title:
--   No p-power torsion in (K^×)^s/Δ K^× in characteristic p
-- statement:
--   Let $K$ be a field of characteristic $p$, where $p$ is a prime (as a natural number carrying a primality instance) and $K$ carries a `CharP K p` instance, and let $n, s$ be natural numbers. Consider the group $(\mathrm{Fin}\ s \to K^\times)$ of $s$-tuples of units of $K$, and inside it the image of the homomorphism `Pi.constMonoidHom (Fin s) Kˣ` sending a unit to the constant tuple with that value, i.e. the diagonal copy $\Delta(K^\times)$. The assertion is that in the quotient group $(K^\times)^s/\Delta(K^\times)$, every element $\xi$ satisfying $\xi^{p^n} = 1$ is equal to $1$; in other words this quotient has no nontrivial $p$-power torsion. The case $s = 0$ is included, the quotient then being trivial, and $n = 0$ is allowed as well.
--
--   The quotient $(K^\times)^s/\Delta(K^\times)$ is the torus occurring as the toric part of the Picard group of a curve with $s$ nodes in a cycle configuration, and the statement says this torus is $p$-divisibly torsion-free in characteristic $p$. It is used in the analysis of fibres of a Deligne–Rapoport model, where it supplies the required absence of $p$-power torsion at a fibre, via [`ModularCurve.DRModelPackage.forall_fibre_pow_torsionFree_algEquivZeroGroupCut`](thm.html#ModularCurve.DRModelPackage.forall_fibre_pow_torsionFree_algEquivZeroGroupCut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem QuotientGroup.eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n s : ℕ)
    (ξ : (Fin s → Kˣ) ⧸ (Pi.constMonoidHom (Fin s) Kˣ).range) (hξ : ξ ^ (p ^ n) = 1) : ξ = 1 := by sorry
