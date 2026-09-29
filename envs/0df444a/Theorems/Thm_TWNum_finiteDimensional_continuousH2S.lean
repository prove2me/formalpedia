-- Prove2me | Theorems.Thm_TWNum_finiteDimensional_continuousH2S
-- name    : TWNum.finiteDimensional_continuousH2S
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/fb8b2046-fe7c-5ff8-8bad-231b1959e2fe
-- title:
--   Finiteness of H² with restricted ramification at level S
-- statement:
--   Let $p$ be a prime (with the primality instance), let $S$ be a finite set of primes containing the prime $p$ itself (as the element `pPrime p` of `Nat.Primes`), and let $M$ be a representation of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the automorphism group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the algebraic closure `AlgebraicClosure ℚ`, on a $\mathbb{Z}/p$-module that is finite-dimensional over $\mathbb{Z}/p$. Two conditions are imposed on $M$: smoothness, namely that every $m \in M$ is fixed by $M.\rho\,s$ for all $s$ in the fixing subgroup of some intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $F/\mathbb{Q}$ finite; and unramifiedness outside $S$, namely that for every prime $q \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, and every $g$ in the image in the full Galois group of the inertia subgroup of $A$ over $\mathbb{Q}$ (pushed forward along the inclusion of the decomposition subgroup), one has $M.\rho\,g = 1$. The conclusion is that `continuousH2S S M` — the quotient of the submodule `levelCocyclesS₂ S M` by the preimage of `levelCoboundariesS₂ S M` under the inclusion of `levelCocyclesS₂ S M` — is finite-dimensional over $\mathbb{Z}/p$.
--
--   This is the finiteness of the second cohomology group $H^2(G_S, M)$ of a finite smooth Galois module unramified outside $S$, in the regime where the residue characteristic $p$ belongs to $S$. It feeds the Euler-characteristic and duality computations for restricted-ramification cohomology used in the Greenberg–Wiles style estimates on Selmer groups and tangent spaces of deformation problems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TWNum_finiteDimensional_continuousH2S.lean

import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem TWNum.finiteDimensional_continuousH2S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    FiniteDimensional (ZMod p) (continuousH2S S M) := by sorry
