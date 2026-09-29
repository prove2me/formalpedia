-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction
-- name    : WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/d9e09234-dd50-5d08-a3bd-3f263e5df327
-- title:
--   Inertial filtration on p^m-torsion at multiplicative reduction
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ and let $p$ be a prime (supplied as a `Fact`) with $p \neq 2$; assume $\Delta_W \neq 0$, $p \mid \Delta_W$ and $p \nmid c_4(W)$. Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime p`, which by the project's definition means that the image of $p$ lies in the nonunits of $A$, and let $m \geq 1$. The points in question are the affine points of $W$ base-changed along $\mathbb Z \to \mathbb Q$ and then to $\overline{\mathbb Q}$, carrying the project's action $\sigma \bullet P =$ `Point.map` $\sigma$ for $\sigma$ in $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$. The theorem asserts the existence of an additive subgroup $F$ of this group of points with four properties. First, $F$ is described exactly: a point $x$ lies in $F$ if and only if $p^m \bullet x = 0$ and `W.InZeroComponentAt A x` holds, the latter being the project's predicate saying that $x = 0$, or $x = (x_0,y_0)$ nonsingular with either $x_0 \notin A$, or $x_0, y_0 \in A$ and the images of $x_0,y_0$ in the residue field of $A$ form a nonsingular point of the reduced curve. Second, $F$ has exactly $p^m$ elements (in particular it is finite; cyclicity is not asserted). Third, $F$ is stable under every $\sigma$ in the decomposition subgroup `A.decompositionSubgroup ℚ`. Fourth, for every $\sigma$ in `A.inertiaSubgroupIn ℚ` (the image in $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ of the inertia subgroup of $A$) and every point $y$ with $p^m \bullet y = 0$, the displacement $\sigma \bullet y - y$ lies in $F$.
--
--   This is the finite-level form, for an integral Weierstrass model with multiplicative reduction at $p$ in the sense $p \mid \Delta$, $p \nmid c_4$, of the statement that the $p^m$-torsion points of the identity component at a place above $p$ form a cyclic group of order $p^m$ on which inertia acts through the cyclotomic character, as read off from the Tate parametrisation; it is the ingredient used in Mazur's reductions. The formal statement is shaped as the existence of one subgroup with an explicit membership criterion, an order count, decomposition-stability and the absorption of all inertial displacements of $p^m$-torsion, rather than as a statement about the Tate curve; cyclicity and the cyclotomic character are not part of the conclusion, and $p \neq 2$ is assumed. It is used in the construction of a stable line with an associated character at a prime of bad reduction ([`WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor`](thm.html#WeierstrassCurve.exists_stableLine_character_of_not_isGoodPrimeFor)) and, through that, in ruling out Galois-stable cofixed lines for Frey curves ([`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
open WeierstrassCurve

theorem WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0)
    (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : ¬ (p : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      (∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        x ∈ F ↔ p ^ m • x = 0 ∧ W.InZeroComponentAt A x) ∧
      Nat.card F = p ^ m ∧
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ F, σ • x ∈ F) ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        p ^ m • y = 0 → σ • y - y ∈ F := by sorry
