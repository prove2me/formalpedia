-- Prove2me | Theorems.Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction
-- name    : WeierstrassCurve.galoisRepUnramifiedAt_of_hasGoodReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/b462b906-a910-59f6-bd54-c261cd1ec02a
-- title:
--   Néron–Ogg–Shafarevich: good reduction gives E[n] unramified at q
-- statement:
--   Let $R$ be a discrete valuation domain equipped with an algebra structure over $\mathbb{Q}$ making $\mathbb{Q}$ its field of fractions, and let $E$ be a Weierstrass curve over $\mathbb{Q}$ carrying an instance of good reduction over $R$ (`E.HasGoodReduction R`). Let $q$ and $n$ be natural numbers, with $q$ prime, with the image of $q$ in $R$ irreducible — so that $q$ is a uniformiser of $R$ — and with $q \nmid n$. The conclusion is the predicate `GaloisRepUnramifiedAt` for $E$, the integer $n$ and the prime $q$, taken with base field $\mathbb{Q}$ and algebraic closure $K = \mathrm{AlgebraicClosure}\ \mathbb{Q}$: for every valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ which lies over $q$ in the sense that the image of $q$ is a non-unit of $A$, for every automorphism $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the image of the inertia subgroup of $A$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup into the full automorphism group, and for every element $x$ of the $\mathbb{Z}$-submodule of $n$-torsion points of the base change of $E$ to $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, one has $\sigma \bullet x = x$.
--
--   This is the accessible direction of the criterion of Néron–Ogg–Shafarevich for elliptic curves: good reduction at $q$ forces the mod-$n$ (and $n$-torsion) Galois representation to be unramified at every place above $q$ when $q \nmid n$. It is used downstream, via [`WeierstrassCurve.galoisRepUnramifiedAt_of_goodReduction`](thm.html#WeierstrassCurve.galoisRepUnramifiedAt_of_goodReduction) and [`WeierstrassCurve.tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor`](thm.html#WeierstrassCurve.tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor), to control the ramification of the Galois representations attached to the Frey curve away from its bad primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.galoisRepUnramifiedAt_of_hasGoodReduction
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (E : WeierstrassCurve ℚ) [E.HasGoodReduction R]
    {q n : ℕ} (hq : q.Prime) (hqR : Irreducible (q : R)) (hqn : ¬ q ∣ n) :
    WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ E n q := by sorry
