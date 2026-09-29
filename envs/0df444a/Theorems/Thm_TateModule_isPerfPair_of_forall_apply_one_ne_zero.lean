-- Prove2me | Theorems.Thm_TateModule_isPerfPair_of_forall_apply_one_ne_zero
-- name    : TateModule.isPerfPair_of_forall_apply_one_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/df7eb402-999e-5519-bf23-4d31806490c3
-- title:
--   Level-one non-degeneracy mod p gives a perfect pairing
-- statement:
--   Let $p$ be a prime and $M$ an additive commutative group, and let $r$ be a natural number such that for every $n$ the $\mathbb{Z}$-submodule of $M$ annihilated by $p^n$ is finite of cardinality $(p^n)^r$. Write $T =$ [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) for the additive subgroup of sequences $x : \mathbb{N} \to M$ satisfying, for every $n$, both $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$, regarded as a $\mathbb{Z}_p$-module. Let $e : T \to T \to \mathbb{Z}_p$ be a $\mathbb{Z}_p$-bilinear form, and assume two non-degeneracy conditions at the first level: for every $a \in T$ whose component $a_1 \in M$ is non-zero there exists $b \in T$ with $e(a,b)$ not divisible by $p$ in $\mathbb{Z}_p$, and for every $b \in T$ whose component $b_1$ is non-zero there exists $a \in T$ with $e(a,b)$ not divisible by $p$. Then $e$ satisfies `LinearMap.IsPerfPair`: both currying maps $a \mapsto e(a,\cdot)$ and $b \mapsto e(\cdot,b)$ are bijections from $T$ onto the $\mathbb{Z}_p$-dual $\operatorname{Hom}_{\mathbb{Z}_p}(T,\mathbb{Z}_p)$.
--
--   This is the algebraic step which upgrades non-degeneracy of a bilinear form on a Tate module modulo $p$ (tested on the first level, i.e. on $p$-torsion) to perfectness of the pairing over $\mathbb{Z}_p$. It is used in the treatment of Riemann forms, in [`AlgebraicGeometry.RiemannForm.perfect_of_forall_torsion_kernelPts_eq_zero`](thm.html#AlgebraicGeometry.RiemannForm.perfect_of_forall_torsion_kernelPts_eq_zero), where the level-$p$ kernel conditions are available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_isPerfPair_of_forall_apply_one_ne_zero.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.isPerfPair_of_forall_apply_one_ne_zero
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (e : TateModule p M →ₗ[ℤ_[p]] TateModule p M →ₗ[ℤ_[p]] ℤ_[p])
    (hleft : ∀ a : TateModule p M, (a : ℕ → M) 1 ≠ 0 → ∃ b : TateModule p M, ¬ (p : ℤ_[p]) ∣ e a b)
    (hright : ∀ b : TateModule p M, (b : ℕ → M) 1 ≠ 0 → ∃ a : TateModule p M, ¬ (p : ℤ_[p]) ∣ e a b) :
    e.IsPerfPair := by sorry
