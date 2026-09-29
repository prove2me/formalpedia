-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_stableLine_character_of_not_isGoodPrimeFor
-- name    : WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/85e000bb-1fb6-5044-a551-7dd2a480b48d
-- title:
--   Stable line and quadratic character at a multiplicative prime
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model, in the sense that for every prime $q$ with $q \mid \Delta_W$ one has $q \nmid c_4(W)$; assume $p$ is not a good prime for $W$, i.e. $p \mid \Delta_W$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (here `AlgebraicClosure ℚ`) lying over $p$, meaning that $p$ belongs to the non-units of $A$. Write $T$ for the $p$-torsion `Submodule.torsionBy ℤ … p` of the group of points of the base change of $W$ to $\mathbb{Q}$ over $\overline{\mathbb{Q}}$, a module over $\mathbb{Z}/p$, on which each $\sigma$ in the decomposition subgroup $D =$ `A.decompositionSubgroup ℚ` acts by the $\mathbb{Z}/p$-linear endomorphism `galoisRepModuleEnd`, namely the endomorphism induced by the Galois action on points. Then there exist a $\mathbb{Z}/p$-submodule $L \subseteq T$ and a monoid homomorphism $\psi : D \to (\mathbb{Z}/p)^{\times}$ such that: $L \neq \bot$ and $L \neq \top$; $L$ is stable under the action of every $\sigma \in D$; for every $\sigma \in D$ and every $v \in T$ one has $\sigma v - \psi(\sigma) v \in L$; for every $\sigma \in D$ and every natural number $a$ such that $\sigma\mu = \mu^{a}$ for all $\mu \in \overline{\mathbb{Q}}$ with $\mu^{p} = 1$, the action of $\sigma$ on each $v \in L$ is multiplication by $a \cdot \psi(\sigma)$ in $\mathbb{Z}/p$; $\psi$ is trivial on the inertia subgroup `A.inertiaSubgroup ℚ`; and $\psi(\sigma)^{2} = 1$ for all $\sigma \in D$.
--
--   This records the local shape, at a prime of multiplicative reduction of a semistable integral model, of the mod $p$ representation attached to the $p$-torsion: the Tate-curve picture, up to an unramified quadratic twist, with an invariant line on which the decomposition group acts by the mod $p$ cyclotomic character times $\psi$ and with $\psi$ giving the action on the quotient. It feeds the verification of the ordinarity condition at primes dividing the discriminant in [`WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_strictOrdinaryCondition_of_dvd_discriminant`](thm.html#WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_strictOrdinaryCondition_of_dvd_discriminant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_stableLine_character_of_not_isGoodPrimeFor.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hbad : ¬ W.IsGoodPrimeFor p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (L : Submodule (ZMod p)
        (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p))
      (ψ : ↥(A.decompositionSubgroup ℚ) →* (ZMod p)ˣ),
      L ≠ ⊥ ∧ L ≠ ⊤ ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ v ∈ L,
        WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
          (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v ∈ L) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        ∀ v : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
              (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v -
            ((ψ σ : (ZMod p)ˣ) : ZMod p) • v ∈ L) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) μ = μ ^ a) →
        ∀ v ∈ L,
          WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
              (W.map (Int.castRingHom ℚ)) p (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v =
            ((a : ZMod p) * ((ψ σ : (ZMod p)ˣ) : ZMod p)) • v) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ), ψ σ ^ 2 = 1) := by sorry
