-- Prove2me | Theorems.Thm_ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit
-- name    : ValuationSubring.exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/61107f4a-7bcc-554e-a0fc-c1722d431f0d
-- title:
--   Descent of unit multiples from the I-adic completion of a valuation ring
-- statement:
--   Let $L$ be a field and $A$ a valuation subring of $L$, and let $I$ be an ideal of $A$ with $I \neq \top$ which is separating in the sense that any $x \in A$ lying in $I^n$ for every natural number $n$ is zero. Let $\alpha, \beta \in A$, and let $u$ be a unit of the $I$-adic completion $\widehat{A} =$ `AdicCompletion I A`, such that the images of $\alpha$ and $\beta$ under the structure map $A \to \widehat{A}$ satisfy $\alpha = \beta\, u$ in $\widehat{A}$. The conclusion is that there exists a unit $v$ of $A$ itself with $\alpha = \beta\, v$ in $A$; that is, a relation of being unit multiples which holds in the completion with a unit of the completion already holds in $A$ with a unit of $A$.
--
--   A descent statement for the relation ‘$\alpha$ and $\beta$ differ by a unit’ along the map from a valuation ring to one of its adic completions, the point being that the unit may be taken in the ring rather than merely in the completion. It is used in the construction of ring homomorphisms out of a valuation subring that are compatible with maps of adic completions over a prime, in [`ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime`](thm.html#ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_of_isUnit
    {L : Type*} [Field L] (A : ValuationSubring L) (I : Ideal ↥A) (hI : I ≠ ⊤)
    (hsep : ∀ x : ↥A, (∀ n : ℕ, x ∈ I ^ n) → x = 0)
    (α β : ↥A) (u : (AdicCompletion I ↥A)ˣ)
    (h : algebraMap (↥A) (AdicCompletion I ↥A) α = algebraMap (↥A) (AdicCompletion I ↥A) β * u) :
    ∃ v : (↥A)ˣ, α = β * v := by sorry
