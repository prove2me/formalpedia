-- Prove2me | Theorems.Thm_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt
-- name    : WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/048103c8-993d-5694-a301-4dc06113057e
-- title:
--   Levelwise unipotent inertia gives unipotent inertia on the Tate module
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Q}$ and $p$ a prime. Assume $\mathrm{hcard}$: for every $n$, the group of $p^n$-torsion points of $W$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ (the $\mathbb{Z}$-submodule killed by $p^n$) has cardinality $(p^n)^2$; this is what makes $W.\mathtt{tateModuleRep}\ p\ \mathrm{hcard}$ available, namely the Galois representation on $\mathtt{TateModule}\ p$ of the point group — the group of sequences $(x_n)$ of points with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — which is free of rank $2$ over $\mathbb{Z}_p$ with the continuous action of $\mathrm{Aut}_{\mathbb{Q}}(\mathrm{AlgebraicClosure}\ \mathbb{Q})$. Let $q$ be a natural number and assume $\mathrm{hgeom}$: for every valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with $q$ a nonunit of $A$, every $\sigma$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\mathrm{AlgebraicClosure}\ \mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$, every $n$, and every $p^n$-torsion point $P$, one has $\sigma\cdot(\sigma\cdot P - P) = \sigma\cdot P - P$. The conclusion is that $W.\mathtt{tateModuleRep}\ p\ \mathrm{hcard}$ satisfies $\mathtt{IsUnipotentOnInertiaAt}\ q$: for every such $A$ and every such $\sigma$, the characteristic polynomial of the endomorphism by which $\sigma$ acts on the Tate module is $(X-1)^2$.
--
--   This is the passage from unipotence of inertia at $q$ on each $p^n$-torsion level to unipotence of inertia on the rank-two $p$-adic Tate-module representation, expressed through the characteristic polynomial $(X-1)^2$. It is used by [`WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction`](thm.html#WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt_of_multiplicativeReduction), where the levelwise hypothesis comes from multiplicative reduction at $q$, and so feeds the local condition at $q$ in the modularity-lifting setup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_tateModuleRep_isUnipotentOnInertiaAt.lean

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.tateModuleRep_isUnipotentOnInertiaAt (W : WeierstrassCurve ℚ) (p : ℕ)
    [Fact p.Prime]
    (hcard : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    {q : ℕ} (hgeom : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ n : ℕ,
        ∀ P ∈ Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ),
          σ • (σ • P - P) = σ • P - P) :
    (W.tateModuleRep p hcard).IsUnipotentOnInertiaAt q := by sorry
