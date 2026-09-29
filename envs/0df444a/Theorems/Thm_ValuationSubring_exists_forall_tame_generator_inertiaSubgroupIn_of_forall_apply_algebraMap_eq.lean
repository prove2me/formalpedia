-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
-- name    : ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/139bbe1b-ef98-5f42-9cbe-c0ee64048da7
-- title:
--   Tame generator of inertia fixing a subfield L
-- statement:
--   Let $q$ be a prime number, let $P$ be a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ satisfying `LiesOverPrime q`, i.e. the image of $q$ in the algebraic closure lies in the set of non-units of $P$, and let $L$ be a field equipped with an algebra structure over which $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ is an $L$-algebra. Write $I$ for `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\,\mathbb{Q}\simeq_{\mathrm{alg}[\mathbb{Q}]}\mathrm{AlgebraicClosure}\,\mathbb{Q}$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup of $P$. Then there exists $\gamma \in I$ which fixes the image of $L$ pointwise, that is $\gamma(\mathrm{algebraMap}\,L\,\overline{\mathbb{Q}}\,l) = \mathrm{algebraMap}\,L\,\overline{\mathbb{Q}}\,l$ for all $l \in L$, with the following property: for every prime $\ell \neq q$, every natural number $m$, and every $\tau \in I$ fixing the image of $L$ pointwise, there are a natural number $j$ and elements $x, w \in I$, each fixing the image of $L$ pointwise, such that $\tau = \gamma^{j} x^{\ell^{m}} w^{\ell^{m}}$. The single element $\gamma$ works simultaneously for all such $\ell$, $m$ and $\tau$.
--
--   This is the statement that inertia at $q$, restricted to the subgroup fixing a prescribed subfield $L$ of $\overline{\mathbb{Q}}$, is generated modulo $\ell^m$-th powers by a single element away from the residue characteristic: the tame quotient is pro-cyclic and the wild part is pro-$q$, so every element is a power of a fixed $\gamma$ times $\ell^m$-th powers. It is used in the analysis of points of $X_1$ over valuation subrings, where the relevant base field is a cyclotomic field $\mathbb{Q}(\zeta_q)$ rather than $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
    {q : ℕ} (hq' : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q)
    (L : Type) [Field L] [Algebra L (AlgebraicClosure ℚ)] :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      (∀ l : L, γ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ∀ (m : ℕ),
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ →
          (∀ l : L, τ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
          ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
            x ∈ P.inertiaSubgroupIn ℚ ∧ (∀ l : L, x (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
            w ∈ P.inertiaSubgroupIn ℚ ∧ (∀ l : L, w (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
            τ = γ ^ j * x ^ (ℓ ^ m) * w ^ (ℓ ^ m) := by sorry
