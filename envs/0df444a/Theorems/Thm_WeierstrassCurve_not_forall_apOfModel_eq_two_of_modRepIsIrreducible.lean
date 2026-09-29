-- Prove2me | Theorems.Thm_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible
-- name    : WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/7d0ff357-f0a5-5fe3-849d-ecc10e3ff1ce
-- title:
--   Irreducible mod p representation forbids a_ℓ ≡ 2 at all such primes
-- statement:
--   Let $p$ be a natural number, assumed prime, with $p \neq 2$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ whose discriminant satisfies $W.\Delta \neq 0$. Assume the hypothesis `ModRepIsIrreducible` for $W$ at $p$: writing $W_{\mathbb{Q}}$ for the base change of $W$ along $\mathbb{Z} \to \mathbb{Q}$ and $T_p$ for the $p$-torsion submodule of the group of points of $W_{\mathbb{Q}}$ over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, the module $T_p$ is nontrivial and every $\mathbb{Z}/p$-submodule of $T_p$ stable under the action of the $\mathbb{Q}$-algebra automorphisms of the algebraic closure is either $\bot$ or $\top$. Let $N'$ be a nonzero natural number and let $S_0$ be a finite set of natural numbers. The conclusion is a negation: it is *not* the case that for every prime $\ell$ with $\ell \notin S_0$, $\ell \equiv 1 \pmod{p N'}$ and $\ell \nmid W.\Delta$ (the predicate `IsGoodPrimeFor`), the image in $\mathbb{Z}/p$ of the integer $a_\ell(W) = \ell + 1 - \#(W \bmod \ell)$, the trace of Frobenius of the reduction of $W$ modulo $\ell$, equals $2$.
--
--   This is the standard consequence of irreducibility of the mod $p$ representation attached to an elliptic curve over $\mathbb{Q}$: the Frobenius traces at good primes congruent to $1$ modulo $pN'$ cannot all be $\equiv 2 \bmod p$, since otherwise the Frobenius elements in the relevant subgroup would all act unipotently and would generate a proper invariant line. It is used as a non-degeneracy input in the construction of mod $p$ eigenclasses in the cohomology $H^1$ with prescribed diamond and Hecke eigenvalues, ruling out the degenerate eigensystem with all $a_\ell \equiv 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible.lean

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (S₀ : Set ℕ) (hS₀fin : S₀.Finite) :
    ¬ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ℓ ≡ 1 [MOD p * N'] → W.IsGoodPrimeFor ℓ →
      ((W.apOfModel ℓ : ℤ) : ZMod p) = 2 := by sorry
