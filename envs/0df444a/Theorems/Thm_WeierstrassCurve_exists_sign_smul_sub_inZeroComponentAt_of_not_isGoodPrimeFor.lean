-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
-- name    : WeierstrassCurve.exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/b55b8f10-d0c0-5442-bf6c-0ab60d3a25b0
-- title:
--   Unramified sign character on p-torsion modulo the zero component
-- statement:
--   Let $p$ be an odd prime and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model, i.e. for every prime $q$ with $q \mid \Delta_W$ one has $q \nmid c_4(W)$, and assume $p$ is not a good prime for $W$, i.e. $p \mid \Delta_W$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, in the sense that the image of $p$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$. Then there is a monoid homomorphism $\psi$ from the decomposition subgroup of $A$ over $\mathbb{Q}$ to $\mathbb{Z}^\times = \{\pm 1\}$ such that $\psi(\sigma) = 1$ for every $\sigma$ in the inertia subgroup, and such that for every $\sigma$ in the decomposition subgroup and every point $y$ of the base change of $W$ to $\overline{\mathbb{Q}}$ with $p \cdot y = 0$, the point $\sigma \cdot y - \psi(\sigma)\, y$ lies in the zero component of $W$ at $A$: it is either the point at infinity, or an affine point $(x,y)$ with $x \notin A$, or an affine point with $x, y \in A$ whose reduction modulo the maximal ideal of $A$ is a nonsingular point of the reduction of $W$ over the residue field of $A$.
--
--   This is the statement that at a prime of multiplicative reduction of a semistable model the decomposition group acts on the $p$-torsion, modulo the points lying in the zero component, through an unramified quadratic character — trivial in the split case and the unramified quadratic character in the non-split case, reflecting the action on the group of components of the special fibre. It feeds the construction of a decomposition-group-stable line in the $p$-torsion, in [`WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor`](thm.html#WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor), used in the analysis of the local behaviour at bad primes of the mod $p$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_sign_smul_sub_inZeroComponentAt_of_not_isGoodPrimeFor
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hbad : ¬ W.IsGoodPrimeFor p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ ψ : ↥(A.decompositionSubgroup ℚ) →* ℤˣ,
      (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ A.inertiaSubgroup ℚ → ψ σ = 1) ∧
      ∀ σ : ↥(A.decompositionSubgroup ℚ),
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p • y = 0 →
          W.InZeroComponentAt A
            ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • y - ((ψ σ : ℤˣ) : ℤ) • y) := by sorry
