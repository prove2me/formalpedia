-- Prove2me | Theorems.Thm_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial
-- name    : WeierstrassCurve.galois_action_trivial_on_submodule_of_inertia_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/de0edd4a-2c05-5e61-93bc-d80513e50a5a
-- title:
--   Everywhere unramified torsion submodule is pointwise Galois-fixed
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Q}$ and let $n$ be a natural number. Write $(W⁄\overline{\mathbb{Q}})$.Point for the group of points of the base change of $W$ to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and let $W[n] =$ `Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n` be its $n$-torsion, which is assumed to be finite. Let $N$ be a $\mathbb{Z}/n$-submodule of $W[n]$. Assume the following unramifiedness hypothesis: for every natural number $q$ that is prime, for every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$, for every element $\sigma$ of the subgroup of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}}^{\mathrm{alg}} \overline{\mathbb{Q}}$ obtained as the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$, and for every $x \in N$, one has $\sigma \bullet x = x$. The conclusion is that then every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ satisfies $\sigma \bullet x = x$ for all $x \in N$, i.e. the whole absolute Galois group of $\mathbb{Q}$ fixes $N$ pointwise.
--
--   This is the Galois-module form of the statement that $\mathbb{Q}$ has no nontrivial everywhere unramified extension (Hermite–Minkowski): a submodule of the $n$-torsion of an elliptic curve over $\mathbb{Q}$ on which all inertia acts trivially is fixed by the full Galois group. It is used by [`FreyPackage.frey_stable_submodule_fixed_or_cofixed`](thm.html#FreyPackage.frey_stable_submodule_fixed_or_cofixed), in the fixed-or-cofixed dichotomy for Galois-stable submodules of the mod $p$ torsion of a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galois_action_trivial_on_submodule_of_inertia_trivial (W : WeierstrassCurve ℚ) {n : ℕ} [Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)] (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ N, σ • x = x) : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x ∈ N, σ • x = x := by sorry
