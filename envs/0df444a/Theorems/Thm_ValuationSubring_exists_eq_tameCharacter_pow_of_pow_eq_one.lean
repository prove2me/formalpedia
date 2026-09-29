-- Prove2me | Theorems.Thm_ValuationSubring_exists_eq_tameCharacter_pow_of_pow_eq_one
-- name    : ValuationSubring.exists_eq_tameCharacter_pow_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/089c68c2-2309-5fd2-873e-249a82ed8c09
-- title:
--   Tame inertia characters of exponent m are powers of the tame character
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $p$ be a prime number, and suppose $P$ lies over $p$ in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $P$. Let $m$ be a natural number with $p \nmid m$, and let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^m = p$. Write $I$ for `P.inertiaSubgroupIn ℚ`, the subgroup of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ obtained as the image of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup of $P$ into the full group of $\mathbb{Q}$-algebra automorphisms. Let $\psi$ be an arbitrary function from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the residue field of $P$ which is multiplicative on $I$, that is $\psi(\sigma\tau) = \psi(\sigma)\psi(\tau)$ for all $\sigma, \tau \in I$, and which satisfies $\psi(\sigma)^m = 1$ for every $\sigma \in I$. Then there is a natural number $j < m$ such that $\psi(\sigma) = \bigl(P.\mathrm{tameCharacter}\,\pi\,\sigma\bigr)^j$ for every $\sigma \in I$, where `P.tameCharacter π` sends $\sigma$ to the residue class of $\sigma(\pi)/\pi$ when this quotient lies in $P$, and to $0$ otherwise. No hypothesis is placed on the values of $\psi$ outside $I$.
--
--   This is the classification of the residue-field-valued characters of the tame quotient of inertia: for $m$ prime to $p$, the tame character attached to an $m$-th root $\pi$ of $p$ exhausts, through its powers, all characters of inertia whose $m$-th power is trivial. Taking $m = q^n - 1$ it identifies the characters of level dividing $n$ as powers of a fundamental character, and it is used in the construction of the inertial characters attached to the residual representation, feeding [`ValuationSubring.exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow`](thm.html#ValuationSubring.exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_eq_tameCharacter_pow_of_pow_eq_one.lean

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_eq_tameCharacter_pow_of_pow_eq_one
    (P : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hP : P.LiesOverPrime p) {m : ℕ} (hpm : ¬ p ∣ m) {π : AlgebraicClosure ℚ} (hπ : π ^ m = p)
    (ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ψ (σ * τ) = ψ σ * ψ τ)
    (hord : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ψ σ ^ m = 1) :
    ∃ j : ℕ, j < m ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ψ σ = P.tameCharacter π σ ^ j := by sorry
