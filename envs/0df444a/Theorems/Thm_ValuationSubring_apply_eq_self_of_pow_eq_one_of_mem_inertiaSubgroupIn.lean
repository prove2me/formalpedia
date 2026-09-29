-- Prove2me | Theorems.Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
-- name    : ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/6dfdd476-a909-5dfe-848c-53e0f610c193
-- title:
--   Inertia at q fixes roots of unity of order prime to q
-- statement:
--   Let $q$ be a prime number and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, that is, the image of $q$ in $\overline{\mathbb{Q}}$ lies in `A.nonunits` (the set of elements of $A$ that are not units of $A$, equivalently the maximal ideal of the valuation ring $A$); so $A$ is a place of $\overline{\mathbb{Q}}$ above $q$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ belonging to `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, under the inclusion of the decomposition subgroup of $A$, of the inertia subgroup of $A$; concretely, $\sigma$ stabilises $A$ and acts trivially on the residue field of $A$. Let $n$ be a natural number with $q \nmid n$ (so in particular $n \neq 0$), and let $\zeta \in \overline{\mathbb{Q}}$ satisfy $\zeta^{n} = 1$. Then $\sigma(\zeta) = \zeta$.
--
--   This is the statement that the group $\mu_n$ of $n$-th roots of unity is unramified at every prime $q$ not dividing $n$, equivalently that the mod-$n$ cyclotomic character is trivial on inertia at such $q$. It is used to show that the determinant of the mod-$\ell$ representation attached to an elliptic curve is trivial on inertia at primes $q \neq \ell$, and in the local analysis at primes of multiplicative reduction via the Tate parametrisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {n : ℕ} (hn : ¬ q ∣ n) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) : σ ζ = ζ := by sorry
