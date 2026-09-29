-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/6d726e5d-9a55-56a2-94a3-5afbd21191a6
-- title:
--   Inertia above an odd prime negates a square root of p
-- statement:
--   Let $p$ be a natural number which is prime and different from $2$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ lies in the set of non-units of $A$ (so $A$ is a place of $\overline{\mathbb{Q}}$ at which $p$ has positive valuation). Let $s \in \overline{\mathbb{Q}}$ satisfy $s^{2} = p$. The assertion is that there exists a $\mathbb{Q}$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}$ such that $\tau$ lies in `A.inertiaSubgroupIn ℚ` — the image in the full group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$ — and such that $\tau(s) = -s$. Thus some element of the inertia group at $A$ acts non-trivially on the quadratic subfield $\mathbb{Q}(\sqrt{p})$, which is the expression of the fact that $\mathbb{Q}(\sqrt{p})/\mathbb{Q}$ is ramified at the odd prime $p$.
--
--   This is the ramification of $\mathbb{Q}(\sqrt{p})$ at an odd prime $p$, in the form of a statement about the inertia subgroup of an arbitrary place of $\overline{\mathbb{Q}}$ above $p$. It is used in the Langlands–Tunnell part of the argument, in the construction of weight-one forms with prescribed local behaviour at a prime whose inertia has order two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_neg_of_sq_eq_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (s : AlgebraicClosure ℚ) (hs : s ^ 2 = (p : AlgebraicClosure ℚ)) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ A.inertiaSubgroupIn ℚ ∧ τ s = -s := by sorry
