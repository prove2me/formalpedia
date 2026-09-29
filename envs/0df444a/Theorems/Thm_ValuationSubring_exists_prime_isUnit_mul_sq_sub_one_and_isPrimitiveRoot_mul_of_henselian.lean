-- Prove2me | Theorems.Thm_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian
-- name    : ValuationSubring.exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b3d89996-7320-58b7-bf32-613f10283a94
-- title:
--   A tame auxiliary prime ℓ and a qℓ-th root of unity
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which lies over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ belongs to the set of non-units of $A$ (so $q \in A$ and $q$ generates a proper ideal). Let $k_0$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ and write $A_0 = A \cap k_0$ for the valuation subring obtained by pulling $A$ back along $k_0 \to \overline{\mathbb{Q}}$; assume $A_0$ is a henselian local ring with algebraically closed residue field. Assume further that $k_0$ contains an element $\zeta_q$ whose image in $\overline{\mathbb{Q}}$ is a primitive $q$-th root of unity, and an element $\varpi_t$ whose image lies in $A$ and satisfies $\varpi_t^{\,q^2-1} = q\,u$ in $\overline{\mathbb{Q}}$ for some unit $u$ of $A$. The conclusion has two parts. First, the relation $\varpi_t^{\,q^2-1} = q\,u$ already holds inside $A_0$ for some unit $u$ of $A_0$, with $\varpi_t$ regarded as an element of $A_0$. Second, there is a prime $\ell$ with $\ell \ge 3$, $\ell \ne q$ and $\ell \nmid M'$, such that the natural number $\ell(\ell^2-1)$ is a unit of $A_0$, together with an element $\xi \in k_0$ which is a primitive $q\ell$-th root of unity in $k_0$, whose image lies in $A$, and a ring homomorphism $\iota : k_0 \to \mathbb{C}$ with $\iota(\xi) = \exp\!\left(2\pi i/(q\ell)\right)$.
--
--   This is the choice of an auxiliary tame level $\ell$ at the prime $q$: the congruence conditions make $\ell(\ell^2-1) = |\mathrm{SL}_2(\mathbb{F}_\ell)|$ invertible in the local ring $A_0$ of residue characteristic $q$, so that the covering of modular curves of level $q\ell$ over level $q$ is tame at $q$, while $\iota$ fixes a complex reading of the chosen $q\ell$-th root of unity. It is used in the construction of supersingular models of modular curves at full level, in [`ModularCurve.FullLevel.exists_supersingularDVR_affineChart_poles_moduliHasse_commonChart_nodes_igusaSep_inertia_of_levelField`](thm.html#ModularCurve.FullLevel.exists_supersingularDVR_affineChart_poles_moduliHasse_commonChart_nodes_igusaSep_inertia_of_levelField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (ζq : ↥k₀) (hζq : IsPrimitiveRoot ((ζq : ↥k₀) : AlgebraicClosure ℚ) q)

    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ)) :

    (∃ u : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit u ∧
      (⟨ϖt, hϖtA⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ^ (q ^ 2 - 1) = (q : _) * u) ∧
    ∃ (ℓ : ℕ), ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
      IsUnit ((ℓ * (ℓ ^ 2 - 1) : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      ∃ ξ : ↥k₀, IsPrimitiveRoot ξ (q * ℓ) ∧ ((ξ : ↥k₀) : AlgebraicClosure ℚ) ∈ A ∧
        ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by sorry
