-- Prove2me | Theorems.Thm_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial
-- name    : WeierstrassCurve.galois_action_trivial_on_quotient_of_inertia_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/1ac17a85-2d68-5ef7-ae42-0530bc802455
-- title:
--   Everywhere unramified action on W[n]/N is trivial
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Q$ and let $n$ be a natural number such that the group $T = \operatorname{torsionBy}_{\mathbb Z}\bigl((W⁄\overline{\mathbb Q}).\mathrm{Point}, n\bigr)$ of $n$-torsion points of $W$ over an algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ is finite. Let $N$ be a $\mathbb Z/n$-submodule of $T$ which is `IsGaloisStable` over $\mathbb Q$, i.e. $\sigma \cdot x \in N$ for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and every $x \in N$. Assume the unramifiedness hypothesis: for every prime number $q$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$ (the predicate `LiesOverPrime`), every $\sigma$ lying in the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ inside its decomposition subgroup, and every $x \in T$, one has $\sigma \cdot x - x \in N$. The conclusion is that the same holds for the whole Galois group: for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and every $x \in T$, $\sigma \cdot x - x \in N$; that is, $(\sigma - 1)T \subseteq N$ for all $\sigma$, so $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ acts trivially on $T/N$.
--
--   This is the quotient-module form of the statement that an everywhere unramified Galois action of $G_{\mathbb Q}$ on a finite module is trivial, since $\mathbb Q$ admits no nontrivial unramified extensions (Minkowski, Hermite–Minkowski). It is used in [`FreyPackage.frey_stable_submodule_fixed_or_cofixed`](thm.html#FreyPackage.frey_stable_submodule_fixed_or_cofixed) to supply the cofixed branch of the dichotomy for a Galois-stable submodule of the torsion of a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.galois_action_trivial_on_quotient_of_inertia_trivial (W : WeierstrassCurve ℚ) {n : ℕ} [Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)] (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n)) (hN : IsGaloisStable (K := AlgebraicClosure ℚ) ℚ N) (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n, σ • x - x ∈ N) : ∀ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∀ x : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point n, σ • x - x ∈ N := by sorry
