-- Prove2me | Theorems.Thm_TateModule_exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy
-- name    : TateModule.exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c4f00f21-bc4d-570e-8866-2bbad29c52d1
-- title:
--   Mittag-Leffler argument with level shift on Tate modules
-- statement:
--   Let $p$ be a prime and let $M$ be an additive commutative group such that for every $n$ the set of $u \in M$ with $p^{n} u = 0$ (the $\mathbb{Z}$-submodule `Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)`, viewed as a subset of $M$) is finite. Let $f : M \to M$ be an additive group homomorphism, let $v$ be a natural number, and let $x$ be an element of [`TateModule p M`](def/EllipticCurve_TateModule.html#L15), that is, a sequence $(x_n)_{n \in \mathbb{N}}$ of elements of $M$ with $p^{n} x_n = 0$ and $p\, x_{n+1} = x_n$ for all $n$, where $x_n$ denotes [`TateModule.proj p M n x`](def/EllipticCurve_TateModule.html#L122). Assume that for every $n$ there exists $z \in M$ with $p^{n+v} z = 0$ and $f(z) = x_n$; no compatibility between these preimages for different $n$ is assumed. The conclusion is that there exists $w$ in [`TateModule p M`](def/EllipticCurve_TateModule.html#L15), i.e. a sequence $(w_n)$ with $p^{n} w_n = 0$ and $p\, w_{n+1} = w_n$, such that $f(w_n) = p^{v} x_n$ for every $n$, the scalars being integers acting on $M$.
--
--   This is the standard passage from levelwise solvability to solvability in the Tate module, with a loss of a factor $p^{v}$: surjectivity statements for $f$ on $p^{n+v}$-torsion, holding separately at each level, are assembled into a single $p$-adic solution of $T_p(f)\,w = p^{v} x$. It is applied with $f = \sigma - 1$ for an inertia element $\sigma$ in the analysis of the toric part of the Tate module of the Jacobian at a place of bad reduction, where it converts a containment of $p^{n}$-torsion in the image of $\sigma - 1$ at each level into a containment of $p^{v}$ times the toric lattice in $(\sigma-1)T_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (hfin : ∀ n : ℕ, (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ) : Set M).Finite)
    (f : M →+ M) (v : ℕ) (x : TateModule p M)
    (hx : ∀ n : ℕ, ∃ z ∈ Submodule.torsionBy ℤ M ((p ^ (n + v) : ℕ) : ℤ), f z = TateModule.proj p M n x) :
    ∃ w : TateModule p M, ∀ n : ℕ, f (TateModule.proj p M n w) = ((p ^ v : ℕ) : ℤ) • TateModule.proj p M n x := by sorry
