-- Prove2me | Theorems.Thm_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
-- name    : UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/39d8f3bb-3e95-5337-8557-2460a230cabf
-- title:
--   Fricke conjugate of U_q as a sum over lower-unipotent cosets
-- statement:
--   Fix a nonzero natural number $N$, an integer $k$, and a nonzero natural number $q$ dividing $N$, together with three functions $G, H, V : \mathfrak H \to \mathbb C$ on the upper half-plane. Two hypotheses relate them through the Fricke substitution of level $N$, each stated for all pairs $\tau, \tau' \in \mathfrak H$ subject to $\tau' \cdot (N\tau) = -1$ (that is, $\tau' = -1/(N\tau)$): first $G(\tau') = \tau^{k} H(\tau)$, and second $(\mathrm{heckeU}\,k\,q\,H)(\tau') = \tau^{k} V(\tau)$, where [`ModularForm.heckeU k q H`](def/ModularForm_HeckeOperator.html#L93) is by definition $\sum_{j<q} H \mid_k M_{q,j}$ with $M_{q,j} \in GL_2(\mathbb R)$ the matrix $\begin{pmatrix} 1 & j \\ 0 & q\end{pmatrix}$ (determinant $q \neq 0$) and $\mid_k$ Mathlib's weight-$k$ slash action. Then for every $\tau \in \mathfrak H$,
--   $$\sum_{j=0}^{q-1} \bigl(G \mid_k S\,T^{\,j\lfloor N/q\rfloor}\,S^{-1}\bigr)(\tau) = q^{1-k}\,(-N)^{-k}\, V\bigl(M_{q,0} \cdot \tau\bigr),$$
--   the slashing matrices being the elements $\begin{pmatrix} 1 & 0 \\ -jN/q & 1\end{pmatrix}$ of $SL_2(\mathbb Z)$ formed from the generators $S$, $T$, the exponent $j\,(N/q)$ being computed with natural division, the complex powers being integer powers, and $M_{q,0}\cdot\tau = \tau/q$. No modularity of $G$, $H$ or $V$ is assumed.
--
--   This is the function-theoretic form of the matrix identity $\begin{pmatrix} 0 & -1 \\ N & 0\end{pmatrix}\begin{pmatrix} 1 & 0 \\ -jN/q & 1\end{pmatrix} = \begin{pmatrix} 1 & j \\ 0 & q\end{pmatrix}\begin{pmatrix} 0 & -1 \\ N/q & 0\end{pmatrix}$, expressing the sum of a weight-$k$ function over the $q$ lower-unipotent cosets attached to $N/q$ as the Fricke conjugate of the operator $U_q$, in the style of the Atkin–Lehner–Li theory of oldforms and $W$-operators. It is used in the analysis of primitive forms, namely in [`CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd`](thm.html#CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd) and [`CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd`](thm.html#CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm in

theorem UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
    (N : ℕ) [NeZero N] (k : ℤ) {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N)
    (G H V : UpperHalfPlane → ℂ)
    (hGH : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      G τ' = (τ : ℂ) ^ k * H τ)
    (hUV : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      ModularForm.heckeU k q H τ' = (τ : ℂ) ^ k * V τ)
    (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        (G ∣[k] (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N / q : ℕ)) * ModularGroup.S⁻¹ :
          SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * (-(N : ℂ)) ^ (-k) * V (ModularForm.heckeMatrix q 0 • τ) := by sorry
