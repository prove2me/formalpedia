-- Prove2me | Theorems.Thm_TateModule_nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow
-- name    : TateModule.nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/75ad2257-f94f-5195-a482-cd868af07501
-- title:
--   Free Tate module of rank r and level surjectivity
-- statement:
--   Let $p$ be a prime, let $M$ be an additive commutative group, and let $r$ be a natural number. Assume that for every $n$ the $p^n$-torsion of $M$, that is the $\mathbb{Z}$-submodule $\{m \in M : p^n m = 0\}$, is of cardinality $(p^n)^r$ (cardinality in the sense of `Nat.card`, so the hypothesis also forces finiteness, the value $(p^n)^r$ being nonzero). Here the Tate module [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) is the additive subgroup of sequences $x : \mathbb{N} \to M$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, carrying its $\mathbb{Z}_p$-module structure. The conclusion is a conjunction: first, the type of $\mathbb{Z}_p$-bases of [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) indexed by `Fin r` is nonempty, i.e. the Tate module is free of rank $r$ over $\mathbb{Z}_p$; second, for every $n$ and every $m \in M$ with $p^n m = 0$ there is an element $x$ of the Tate module whose underlying sequence satisfies $x_n = m$, so each projection from the Tate module to the $p^n$-torsion of $M$ is surjective.
--
--   This is the standard structure statement for the $p$-adic Tate module of a group whose $p^n$-torsion has exactly $(p^n)^r$ elements, as for $A(\bar k)$ with $r = 2g$: freeness of rank $r$ over $\mathbb{Z}_p$ together with surjectivity of each level map. It is used in the treatment of Riemann forms and level pairings, for instance by [`AlgebraicGeometry.RiemannForm.eq_zero_iff_forall_nonempty_pullback_translation_iso`](thm.html#AlgebraicGeometry.RiemannForm.eq_zero_iff_forall_nonempty_pullback_translation_iso) and [`AlgebraicGeometry.RiemannForm.isLevelPairingValue_one_of_forall_dvd`](thm.html#AlgebraicGeometry.RiemannForm.isLevelPairingValue_one_of_forall_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Nonempty (Module.Basis (Fin r) ℤ_[p] (TateModule p M)) ∧
    ∀ (n : ℕ) (m : M), ((p ^ n : ℕ) : ℤ) • m = 0 → ∃ x : TateModule p M, (x : ℕ → M) n = m := by sorry
