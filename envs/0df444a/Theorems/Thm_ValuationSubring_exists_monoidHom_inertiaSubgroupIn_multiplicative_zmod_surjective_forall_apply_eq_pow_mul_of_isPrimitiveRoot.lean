-- Prove2me | Theorems.Thm_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
-- name    : ValuationSubring.exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/8927f208-c8a3-534a-a46b-133d8bd39c3d
-- title:
--   Tame Kummer character of inertia valued in ℤ/m
-- statement:
--   Let $r$ be a prime number and $m$ a nonzero natural number with $r \nmid m$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $r$, in the sense that the image of $r$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, and let $\zeta \in \overline{\mathbb{Q}}$ be a primitive $m$-th root of unity. Write $I_A$ for `A.inertiaSubgroupIn ℚ`, the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\text{alg}[\mathbb{Q}]} \overline{\mathbb{Q}}$ obtained as the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$. Then there exists a monoid homomorphism $t \colon I_A \to \mathrm{Multiplicative}(\mathbb{Z}/m\mathbb{Z})$ which is surjective and satisfies the following Kummer law: for every $\sigma \in I_A$ and every $x \in \overline{\mathbb{Q}}$ with $x^m = r$, one has $\sigma(x) = \zeta^{\,n(\sigma)} x$, where $n(\sigma)$ is the canonical representative in $\{0,\dots,m-1\}$ (the value of `ZMod.val`) of the class $t(\sigma) \in \mathbb{Z}/m\mathbb{Z}$ read additively.
--
--   This is the tame (Kummer) character of inertia at a place above $r$, written with values in $\mathbb{Z}/m\mathbb{Z}$ rather than in $\mu_m$, the identification being fixed by the chosen primitive root $\zeta$. It is used in the $r$-adic period uniformisation of Čerednik–Drinfel'd/Mumford curves, where it supplies the tame character and its surjectivity together with the identification of torsion of the torus by the same $\zeta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_monoidHom_inertiaSubgroupIn_multiplicative_zmod_surjective_forall_apply_eq_pow_mul_of_isPrimitiveRoot
    {r : ℕ} (hr : r.Prime) {m : ℕ} [NeZero m] (hrm : ¬ r ∣ m)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ m) :
    ∃ t : ↥(A.inertiaSubgroupIn ℚ) →* Multiplicative (ZMod m),
      Function.Surjective t ∧
      ∀ (σ : ↥(A.inertiaSubgroupIn ℚ)) (x : AlgebraicClosure ℚ), x ^ m = (r : AlgebraicClosure ℚ) →
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x = ζ ^ (Multiplicative.toAdd (t σ)).val * x := by sorry
