-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
-- name    : WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/dbf7395f-26c4-5e20-9962-f1509d5fca83
-- title:
--   ℓ-torsion in the zero component at a multiplicative prime
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $q$ be a prime, and assume $\Delta(W)\neq 0$, $q \mid \Delta(W)$ and $q \nmid c_4(W)$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that $q$ is a nonunit of $A$, and let $\ell$ be a prime. Write $E$ for the curve $W$ base changed along $\mathbb{Z}\to\mathbb{Q}$ and then to $\overline{\mathbb{Q}}$, and $E[\ell] =$ `Submodule.torsionBy ℤ E.Point ℓ` for its group of $\ell$-torsion points, regarded as a module over $\mathbb{Z}/\ell$. Then there is a $\mathbb{Z}/\ell$-submodule $M \subseteq E[\ell]$ with the following three properties. First, a point $P \in E[\ell]$ lies in $M$ if and only if `W.InZeroComponentAt A P` holds, i.e. either $P = 0$, or $P$ is an affine point $(x,y)$ with $x \notin A$, or $P=(x,y)$ with $x,y \in A$ whose images under the residue map $A \to A/\mathfrak{m}_A$ form a nonsingular point of the reduction of $W$ over the residue field of $A$. Second, $M$ is stable under the action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ belonging to the decomposition subgroup of $A$. Third, if $\ell \neq q$, then every element of the image of the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixes each element of $M$.
--
--   This is the statement, at a prime $q$ of multiplicative (nodal) reduction, that the $\ell$-torsion lying in the zero component at a place above $q$ is a line stable under the decomposition group and pointwise fixed by inertia when $\ell \neq q$ — in Tate-curve terms the image of $\mu_\ell$ in $\overline{\mathbb{Q}}_q^\times/t^{\mathbb{Z}}$. It supplies the unramified sub-line used by the Frey-package lemmas on the local behaviour of the mod $\ell$ representation at primes dividing $abc$, in particular the filtration and no-cofixed-line arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ M : Submodule (ZMod ℓ) (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ),
      (∀ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ, P ∈ M ↔ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) ∧
      (∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), σ ∈ A.decompositionSubgroup ℚ →
        ∀ x ∈ M, σ • x ∈ M) ∧
      (ℓ ≠ q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ M, σ • x = x) := by sorry
