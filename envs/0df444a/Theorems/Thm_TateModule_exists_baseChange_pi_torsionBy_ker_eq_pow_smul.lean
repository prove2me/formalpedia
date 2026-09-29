-- Prove2me | Theorems.Thm_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul
-- name    : TateModule.exists_baseChange_pi_torsionBy_ker_eq_pow_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/90136aa7-a3c9-5f46-a70c-750aa924115c
-- title:
--   A level-n coordinate map on R⊗_{mathbb Z_p}TₚM with kernel pⁿ
-- statement:
--   Let $p$ be a prime and $M$ an abelian group, and let $T_pM$ denote the additive subgroup [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) of the group of sequences $\mathbb N\to M$ consisting of those $x$ with $p^n\cdot x_n=0$ and $p\cdot x_{n+1}=x_n$ for all $n$ (the integers acting by the $\mathbb Z$-module structure), regarded as a $\mathbb Z_p$-module. Let $R$ be a commutative ring equipped with a $\mathbb Z_p$-algebra structure which is finite and free as a $\mathbb Z_p$-module, and let $n\in\mathbb N$. The assertion is that there exists an additive map $\lambda$ from $R\otimes_{\mathbb Z_p}T_pM$ to the functions $\mathrm{Fin}\,b\to M[p^n]$, where $b=\operatorname{rank}_{\mathbb Z_p}R$ is `Module.finrank` and $M[p^n]$ is the submodule `Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)` of elements killed by $p^n$, such that: (a) for every $z$, one has $\lambda(z)=0$ if and only if $z=(p:R)^n\cdot w$ for some $w\in R\otimes_{\mathbb Z_p}T_pM$; and (b) for every monoid $G$ acting on $M$ by additive maps, every $g\in G$, every $z$ and every index $i$, the element of $M$ underlying the $i$-th component of $\lambda$ applied to the base change along $R$ of the endomorphism [`TateModule.rep p M G g`](def/EllipticCurve_TateModule.html#L174) of $T_pM$ (acting termwise by $g$) evaluated at $z$ equals $g$ applied to the element of $M$ underlying the $i$-th component of $\lambda(z)$.
--
--   This records the elementary mechanism by which the finite levels of an $\mathbb Z_p[\,\cdot\,]$-lattice built from a Tate module embed, equivariantly for any monoid acting on $M$, into a finite power of the $p^n$-torsion of $M$: after a choice of $\mathbb Z_p$-basis of $R$ the quotient $(R\otimes_{\mathbb Z_p}T_pM)/p^n$ sits inside $M[p^n]^b$. It is used in the construction of a faithful Galois–Hecke lattice at finite level with prescribed Frobenius behaviour at primes not dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

theorem TateModule.exists_baseChange_pi_torsionBy_ker_eq_pow_smul
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M]
    (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    (n : ℕ) :
    ∃ lam : R ⊗[ℤ_[p]] ↥(TateModule p M) →+
        (Fin (Module.finrank ℤ_[p] R) → ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))),
      (∀ z : R ⊗[ℤ_[p]] ↥(TateModule p M),
        lam z = 0 ↔ ∃ w : R ⊗[ℤ_[p]] ↥(TateModule p M), z = ((p : R) ^ n) • w) ∧
      ∀ (G : Type) [Monoid G] [DistribMulAction G M] (g : G) (z : R ⊗[ℤ_[p]] ↥(TateModule p M))
        (i : Fin (Module.finrank ℤ_[p] R)),
        ((lam ((TateModule.rep p M G g).baseChange R z) i :
            ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) =
          g • ((lam z i : ↥(Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ))) : M) := by sorry
