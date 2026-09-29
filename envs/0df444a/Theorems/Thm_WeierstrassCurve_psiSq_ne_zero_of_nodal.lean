-- Prove2me | Theorems.Thm_WeierstrassCurve_psiSq_ne_zero_of_nodal
-- name    : WeierstrassCurve.psiSq_ne_zero_of_nodal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/a929ac2d-0e24-55a5-829d-679987b6e7f3
-- title:
--   Nonvanishing of Ψ^{sq}ₚ for a nodal cubic in characteristic p
-- statement:
--   Let $k$ be a field, let $p$ be a prime number, and suppose $k$ has characteristic $p$. Let $W$ be a Weierstrass curve over $k$, given by coefficients $a_1,a_2,a_3,a_4,a_6 \in k$, and assume that its discriminant vanishes, $\Delta(W)=0$, while $c_4(W)\neq 0$; thus $W$ is a singular Weierstrass cubic whose singularity is a node rather than a cusp. The conclusion is that the univariate division polynomial $\Psi^{\mathrm{sq}}_p(W)$ attached to $W$ and to $p$ — the element of $k[X]$ that represents the square $\psi_p^2$ of the $p$-th division polynomial modulo the Weierstrass equation — is not the zero polynomial. Note that the statement is not vacuous precisely because the characteristic divides $p$: in characteristic $0$ the polynomial $\Psi^{\mathrm{sq}}_p$ has degree $p^2-1$ with leading coefficient $p^2$, whereas here that leading coefficient vanishes, so non-vanishing of the whole polynomial is a genuine assertion about the remaining coefficients.
--
--   This is the statement that, for a nodal Weierstrass cubic in characteristic $p$, multiplication by $p$ kills no nonsingular point, reflecting the fact that the smooth locus of such a cubic is a form of the multiplicative group, on which multiplication by $p$ is injective. It is used in the construction of $p$-torsion points lying inside and outside the identity component of the special fibre, namely by [`WeierstrassCurve.exists_torsionBy_residueChar_ne_zero_inZeroComponentAt`](thm.html#WeierstrassCurve.exists_torsionBy_residueChar_ne_zero_inZeroComponentAt) and [`WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt`](thm.html#WeierstrassCurve.exists_torsionBy_residueChar_not_inZeroComponentAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_psiSq_ne_zero_of_nodal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.psiSq_ne_zero_of_nodal {k : Type*} [Field k] {p : ℕ} (hp : p.Prime) [CharP k p] (W : WeierstrassCurve k) (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) : W.ΨSq p ≠ 0 := by sorry
