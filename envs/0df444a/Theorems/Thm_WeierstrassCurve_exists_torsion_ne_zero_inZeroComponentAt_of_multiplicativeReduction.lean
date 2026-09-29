-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction
-- name    : WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/c8a5390d-d152-506c-b18b-e2201920d253
-- title:
--   Nonzero ℓ-torsion in the zero component at a multiplicative prime
-- statement:
--   Let $W$ be a Weierstrass equation over $\mathbb{Z}$ with non-vanishing discriminant $\Delta(W) \neq 0$, let $q$ be a prime number with $q \mid \Delta(W)$ and $q \nmid c_4(W)$, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in $A$ is a non-unit of $A$, and let $\ell$ be a prime number. Write $E$ for the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$ and then to $\overline{\mathbb{Q}}$, and $E(\overline{\mathbb{Q}})$ for its group of points. Then the $\ell$-torsion submodule $\{P : \ell P = 0\}$ of $E(\overline{\mathbb{Q}})$ contains an element $P$ with $P \neq 0$ such that `W.InZeroComponentAt A P` holds, that is: either $P = 0$, or $P$ is an affine nonsingular point $(x,y)$ for which either $x \notin A$, or both $x, y \in A$ and the pair of their images under the residue map $A \to A/\mathfrak{m}_A$ is a nonsingular point of the Weierstrass equation obtained from $W$ by reduction to the residue field of $A$. Since the produced $P$ is nonzero, one of the two latter alternatives holds for it.
--
--   This says that at a prime $q$ of multiplicative (nodal) reduction the intersection $E[\ell] \cap E^0_A$ of the $\ell$-torsion with the zero component at a place $A$ above $q$ is nonzero, for every prime $\ell$, including $\ell = q$. It feeds the construction of filtrations of the torsion at all primes of multiplicative reduction, used in [`WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction_all_primes`](thm.html#WeierstrassCurve.exists_atP_filtration_of_multiplicativeReduction_all_primes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction.lean

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

theorem WeierstrassCurve.exists_torsion_ne_zero_inZeroComponentAt_of_multiplicativeReduction
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ P : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ℓ, P ≠ 0 ∧ W.InZeroComponentAt A (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := by sorry
