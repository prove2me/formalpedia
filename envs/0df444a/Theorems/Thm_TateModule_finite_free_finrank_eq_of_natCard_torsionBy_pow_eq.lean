-- Prove2me | Theorems.Thm_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
-- name    : TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/0eda69a3-589a-56a7-82e6-d8704504adae
-- title:
--   Tate module of ℓ-power torsion of order (ℓⁿ)ᵈ is free of rank d
-- statement:
--   Let $\ell$ be a prime, let $M$ be an additive abelian group and let $d$ be a natural number. Assume that for every $n$ the $\mathbb{Z}$-torsion submodule $\mathrm{torsionBy}\,\mathbb{Z}\,M\,\ell^n$, that is the subgroup $M[\ell^n]$ of elements killed by the integer $\ell^n$, satisfies $\mathrm{Nat.card}\,M[\ell^n] = (\ell^n)^d$ (since $(\ell^n)^d \neq 0$, this in particular forces each $M[\ell^n]$ to be finite). Here [`TateModule ℓ M`](def/EllipticCurve_TateModule.html#L15) is the additive subgroup of sequences $x : \mathbb{N} \to M$ such that for all $n$ one has $\ell^n \cdot x_n = 0$ and $\ell \cdot x_{n+1} = x_n$, i.e. the inverse limit $\varprojlim_n M[\ell^n]$ along multiplication by $\ell$, carrying its $\mathbb{Z}_{[\ell]}$-module structure, and [`ModularCurve.RationalTateModule ℓ M`](def/ModularCurve_JZeroTateModule.html#L45) is the base change $\mathbb{Q}_{[\ell]} \otimes_{\mathbb{Z}_{[\ell]}} \mathrm{TateModule}\,\ell\,M$. The conclusion is the conjunction of four assertions: [`TateModule ℓ M`](def/EllipticCurve_TateModule.html#L15) is a finite $\mathbb{Z}_\ell$-module, it is a free $\mathbb{Z}_\ell$-module, its $\mathbb{Z}_\ell$-rank is $d$, and the $\mathbb{Q}_\ell$-dimension of $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} \mathrm{TateModule}\,\ell\,M$ is $d$.
--
--   This is the standard structural description of an $\ell$-adic Tate module: a purely group-theoretic counting hypothesis on the $\ell$-power torsion levels identifies the Tate module as $\mathbb{Z}_\ell^d$ and its rational companion as a $d$-dimensional $\mathbb{Q}_\ell$-vector space. It is used in the project wherever Tate modules of abelian groups of geometric origin must be known to be free of a prescribed rank, for instance in the lemmas on the action of inertia on torsion points of curves and on Tate modules of abelian varieties with quaternionic multiplication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_finite_free_finrank_eq_of_natCard_torsionBy_pow_eq.lean

import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem TateModule.finite_free_finrank_eq_of_natCard_torsionBy_pow_eq
    (ℓ : ℕ) [Fact ℓ.Prime] (M : Type) [AddCommGroup M] (d : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ d) :
    Module.Finite ℤ_[ℓ] (TateModule ℓ M) ∧ Module.Free ℤ_[ℓ] (TateModule ℓ M) ∧
      Module.finrank ℤ_[ℓ] (TateModule ℓ M) = d ∧
      Module.finrank ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ M) = d := by sorry
