-- Prove2me | Theorems.Thm_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
-- name    : UniqueFactorizationMonoid.dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/4066a29a-1c91-5dc7-98f7-eb5a610545e2
-- title:
--   Unramifiedness forces e ∣ vₚ(f) for an e-th root
-- statement:
--   Let $R$ be a Noetherian unique factorisation domain (a commutative domain with unique factorisation and the Noetherian property), let $p \in R$ be a prime element, let $e$ be a natural number with $e > 0$, and let $f \in R$ be nonzero. Let $B$ be a Noetherian integrally closed domain which is an $R$-algebra, module-finite over $R$, with the structure map $R \to B$ injective (the `FaithfulSMul` hypothesis). Let $K_0$ be a field that is a fraction field of $R$, and let $F$ be a field which is simultaneously a $K_0$-algebra and an $R$-algebra compatibly over $R$, and a $B$-algebra compatibly over $R$, such that $F$ is a fraction field of $B$. Suppose $\alpha \in F$ satisfies $\alpha^e = f$ (the image of $f$ under $R \to F$), and suppose that for every prime ideal $\mathfrak{P}$ of $B$ whose contraction along $R \to B$ equals the ideal $(p) = \mathrm{span}\{p\}$, the algebra $B$ is unramified over $R$ at $\mathfrak{P}$ in the sense of `Algebra.IsUnramifiedAt R 𝔓`. Then $e$ divides $\mathrm{multiplicity}\ p\ f$, the multiplicity of $p$ in $f$.
--
--   This is the valuation half of the Kummer-theoretic input to Abhyankar-type arguments: an $e$-th root of $f$ can only generate an extension unramified over the prime $p$ if $e$ divides the $p$-adic multiplicity of $f$, with no hypothesis on roots of unity or on $e$. It is used in the construction of an algebra isomorphism with $\mathrm{AdjoinRoot}(X^e - c)$ for cyclic unramified extensions of a regular local ring, via [`IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot`](thm.html#IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UniqueFactorizationMonoid_dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem UniqueFactorizationMonoid.dvd_multiplicity_of_pow_eq_algebraMap_of_forall_isUnramifiedAt
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (p : R) (hp : Prime p) (e : ℕ) (he : 0 < e) (f : R) (hf : f ≠ 0)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    (α : F) (hα : α ^ e = algebraMap R F f)
    (hunr : ∀ (𝔓 : Ideal B) [𝔓.IsPrime], 𝔓.comap (algebraMap R B) = Ideal.span {p} → Algebra.IsUnramifiedAt R 𝔓) :
    e ∣ multiplicity p f := by sorry
