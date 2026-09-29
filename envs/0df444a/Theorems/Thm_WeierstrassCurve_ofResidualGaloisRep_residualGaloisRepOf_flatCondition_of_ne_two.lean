-- Prove2me | Theorems.Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two
-- name    : WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/dfcb68c6-4f41-5029-88b5-a06ebaccdede
-- title:
--   Flat condition for mod p torsion at odd good primes
-- statement:
--   Fix a commutative ring $\mathcal{O}$, a finite field $k$ which is an $\mathcal{O}$-algebra, a Weierstrass model $W$ over $\mathbb{Z}$, a prime $p$ with $p \neq 2$, and a ring homomorphism $\iota : \mathbb{Z}/p \to k$. Assume: $p$ is a good prime for $W$ in the project's sense, namely $p \nmid \Delta_W$ (`IsGoodPrimeFor`); the $p$-torsion of the points of $W_{\mathbb{Q}} = W \otimes \mathbb{Q}$ over $\overline{\mathbb{Q}}$ has exactly $p^2$ elements (`hcard`); and the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on that $p$-torsion, as the monoid homomorphism `galoisRepModuleEnd`, is trivial on the subgroup fixing some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ (`hker`). Finally let $S$ be a finite set of natural numbers — not required to consist of primes — with $p \in S$ and such that every prime $q \notin S$ satisfies $q \nmid \Delta_W$. The conclusion is that the residual representation $\bar\rho$ cut out by these data on the $p$-torsion, base changed along $\iota$ to $k$ and then regarded as an object of [`GaloisRepAdic k`](def/GaloisRep_Adic.html#L16), satisfies [`GaloisRep.flatCondition 𝒪 p S`](def/GaloisRep_Flat.html#L47); by definition this is the conjunction of three assertions: its determinant is cyclotomic in the project's sense (`DetIsCyclotomic p`), it is flat at $p$ in the project's sense (`IsFlatAt p`: the residue field is finite and, for every ideal $I$ of coefficients with finite quotient, the quotient $V/IV$ is Galois-equivariantly isomorphic, as a group under convolution, to the $\overline{\mathbb{Q}}$-points of some finite flat cocommutative Hopf algebra over the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$), and it is unramified at every prime $q \notin S$. Nothing is asserted when $p = 2$.
--
--   Classically this is the statement that for an elliptic curve over $\mathbb{Q}$ with good reduction at $p$ the representation on $p$-torsion is of flat (finite flat) type at $p$, unramified outside the bad primes, with cyclotomic determinant by the Weil pairing; the flat type condition is Serre's weight-two condition and the corresponding deformation problem is Wiles's flat case. The formal statement differs from the textbook one in that good reduction is taken in the naive form $p \nmid \Delta_W$ for the given integral model, the $p$-torsion is handled through the hypotheses `hcard` and `hker` rather than through a theory of the Tate module, flatness at $p$ is the project's `IsFlatAt` predicate, and $S$ is any finite set of naturals containing $p$ and all primes dividing $\Delta_W$. It is a specialisation to odd $p$ of the corresponding all-primes statement, which it does not prove. It feeds the construction of deformation data for the flat condition for semistable curves at odd non-ordinary primes, and through that the patching input to modularity lifting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.ofResidualGaloisRep_residualGaloisRepOf_flatCondition_of_ne_two
    (𝒪 : Type) [CommRing 𝒪] {k : Type} [Field k] [Finite k] [Algebra 𝒪 k]
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ι : ZMod p →+* k)
    (hgood : W.IsGoodPrimeFor p)
    (hcard : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    {S : Finset ℕ} (hpS : p ∈ S) (hS : ∀ q : ℕ, q.Prime → q ∉ S → W.IsGoodPrimeFor q) :
    GaloisRep.flatCondition 𝒪 p S (GaloisRepAdic.ofResidualGaloisRep
      (((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard hker).baseChangeAlong ι)) := by sorry
