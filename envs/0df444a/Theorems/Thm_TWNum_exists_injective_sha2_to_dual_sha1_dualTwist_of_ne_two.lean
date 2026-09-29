-- Prove2me | Theorems.Thm_TWNum_exists_injective_sha2_to_dual_sha1_dualTwist_of_ne_two
-- name    : TWNum.exists_injective_sha2_to_dual_sha1_dualTwist_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/3557d483-c220-5620-8b6c-a2b9f9ac9822
-- title:
--   Injection of Ш²_S(M) into the dual of Ш¹_S(M^∨(1))
-- statement:
--   Fix a prime $p$ (as a `Fact`) with $p \neq 2$, a finite set $S$ of prime numbers such that the element `pPrime p` of `Nat.Primes` determined by $p$ lies in $S$, and a representation $M$ of the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the automorphism group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of `AlgebraicClosure ℚ`, on a finite-dimensional $\mathbb{Z}/p$-vector space. Two arithmetic hypotheses are imposed on $M$: smoothness, namely that every $m \in M$ admits an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $F/\mathbb{Q}$ finite such that $M.\rho(s)\,m = m$ for all $s$ in the fixing subgroup of $F$; and unramifiedness outside $S$, namely that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$ (the predicate `LiesOverPrime`), every $g$ in the image `inertiaSubgroupIn ℚ` of the inertia subgroup of $A$ inside the decomposition subgroup acts as the identity on $M$. The conclusion asserts the existence of a $\mathbb{Z}/p$-linear map from `sha₂ S M` to the $\mathbb{Z}/p$-linear dual of `sha₁ S (M.dualTwist (cycloChar p))`, which is injective; here `M.dualTwist (cycloChar p)` is the linear dual representation $M^\vee$ with $g$ acting by $\chi(g)$ times its dual action, $\chi$ being the mod $p$ cyclotomic character of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained from `modularCyclotomicCharacter`.
--
--   This is the one-sided, linear-map form of Poitou–Tate duality for the Tate–Shafarevich groups attached to $S$: the nondegenerate pairing $Ш^1_S(M^\vee(1)) \times Ш^2_S(M) \to \mathbb{Z}/p$ is repackaged as an embedding of $Ш^2_S(M)$ into the dual of $Ш^1_S(M^\vee(1))$. It feeds the comparison of dimensions [`groupCohomology.finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two`](thm.html#groupCohomology.finrank_sha1_dualTwist_eq_finrank_sha2_of_ne_two), used in the numerical bookkeeping on the way to the Taylor–Wiles identification $R = T$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TWNum_exists_injective_sha2_to_dual_sha1_dualTwist_of_ne_two.lean

import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem TWNum.exists_injective_sha2_to_dual_sha1_dualTwist_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∃ f : sha₂ S M →ₗ[ZMod p] Module.Dual (ZMod p) (sha₁ S (M.dualTwist (cycloChar p))),
      Function.Injective f := by sorry
