-- Prove2me | Theorems.Thm_Rudin_ch10_stokes_simplex
-- name    : Rudin.ch10_stokes_simplex
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T02:49:06.37169+00:00
-- url     : https://prove2.me/theorems/632fa627-0765-46f3-b4b1-588430cbdae7
-- title:
--   Stokes' formula on the standard simplex $Q^{k+1}$
-- statement:
--   Stokes' formula on the standard simplex, the analytic core of Rudin's Theorem 10.33.
--
--   Let $k\ge 0$ and let
--   $$\omega = \sum_{i_1,\dots,i_k} a_{i_1\cdots i_k}\,dx_{i_1}\wedge\cdots\wedge dx_{i_k}$$
--   be a $k$-form in $\mathbb{R}^{k+1}$ whose coefficient functions are of class $C'$ on all of
--   $\mathbb{R}^{k+1}$. Let $\sigma$ denote the oriented affine simplex
--   $[\mathbf{0},\mathbf{e}_1,\dots,\mathbf{e}_{k+1}]$, i.e. the $(k+1)$-surface with parameter
--   domain $Q^{k+1}$ given by the identity map of $Q^{k+1}$ (the affine map
--   $u\mapsto \sum_i u_i\mathbf{e}_i$ is the identity). Then
--   $$\int_\sigma d\omega = \int_{\partial\sigma}\omega,$$
--   where $\partial\sigma=\sum_{j=0}^{k+1}(-1)^j\,\sigma\circ(\text{$j$-th face})$ is the boundary
--   $k$-chain of Rudin's Definition 10.30, obtained by deleting the $j$-th vertex of
--   $[\mathbf{0},\mathbf{e}_1,\dots,\mathbf{e}_{k+1}]$.
--
--   This is exactly the computation Rudin carries out on pp. 273-274: after expanding the Jacobian
--   of the identity along the index tuples, the left-hand side becomes an integral over $Q^{k+1}$ of
--   a signed sum of first-order partial derivatives of the coefficients, and the fundamental theorem
--   of calculus applied in each coordinate direction, together with the iterated-integral theorem,
--   converts it into the alternating sum of the integrals over the $k+2$ faces of $Q^{k+1}$.
--
--   Every other ingredient of Stokes' theorem for a general chain is formal: a chain is integrated
--   term by term, a general $(m+1)$-surface $\Phi$ is reduced to this case by pulling $\omega$ back
--   along $\Phi$ (Rudin's Theorems 10.22(c) and 10.25), and the faces of $\Phi$ are the composites of
--   $\Phi$ with the faces of $Q^{m+1}$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, Theorem 10.33 (Stokes' theorem), pp. 273-274 (the case of the oriented affine simplex [0, e_1, ..., e_{k+1}]), together with Definition 10.30 (boundary of a surface)

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.33 (Stokes' theorem), the case of the identity surface of the standard
simplex: if `ω` is a `k`-form of class `C'` in `ℝ^{k+1}`, then the integral of `dω` over the
oriented simplex `Q^{k+1}` equals the integral of `ω` over its boundary chain. -/
theorem ch10_stokes_simplex (k : ℕ) (ω : KForm k (k + 1)) (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) :
    integralOverSimplex (extDeriv ω) ⟨id⟩ = Chain.integral ω (surfaceBoundary ⟨id⟩) := by sorry

end Rudin
