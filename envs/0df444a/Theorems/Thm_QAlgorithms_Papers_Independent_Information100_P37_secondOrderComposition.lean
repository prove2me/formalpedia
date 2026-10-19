-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P37_secondOrderComposition
-- name    : QAlgorithms.Papers.Independent.Information100.P37.secondOrderComposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:13:01.628859+00:00
-- url     : https://prove2.me/theorems/ae32a888-6ea2-4d15-b569-756343513a4d
-- title:
--   Proposition 13, Second-order composition data
-- statement:
--   Fix a reference orthonormal basis of a finite-dimensional complex Hilbert space of dimension $d\ge1$. For a population vector $p$ in the closed simplex $\{p_i\ge0,\ \sum_i p_i=1\}$, let $\rho_p=\operatorname{diag}p$. The input law $\nu_d=\operatorname{Dir}(1,\ldots,1)$ is uniform on this whole simplex. Write $c_B(\rho)=\sum_{i\ne j}|\rho_{ij}|^2$ for squared Hilbert–Schmidt coherence. For a fixed unitary $U$, set $X_U(p)=c_B(U\rho_pU^\dagger)$, $C_U=\mathbb E_{\nu_d}X_U$, $\Delta_U=\sqrt{\operatorname{Var}_{\nu_d}X_U}$, $P_{ij}=|U_{ij}|^2$, $G=I-P^TP$, $H_d=I-\mathbf1\mathbf1^T/d$, and $D_d=d(d+1)(d+2)(d+3)$.
--
--   Let $U,V$ be unitaries on dimensions $m,n\ge1$, in the product reference basis, and let $A=G_U$, $B=G_V$, $G=G_{U\otimes V}$. Set $t_A=\operatorname{Tr}A$, $q_A=\operatorname{Tr}(A^2)$, $h_A=\sum_iA_{ii}^2$, with analogous definitions for $B$ and $G$. Then
--   $$\begin{aligned}t_G&=mn-(m-t_A)(n-t_B),\\q_G&=mn-2(m-t_A)(n-t_B)+(m-2t_A+q_A)(n-2t_B+q_B),\\h_G&=nh_A+mh_B+h_Ah_B+2t_At_B-2h_At_B-2t_Ah_B.\end{aligned}$$
--   Here $m,n$ are the subsystem dimensions, and the reference basis is their product.
--
--   The three computed invariants determine the second coherence moment of the product.
-- source:
--   Coherence -generating power deviation: Fluctuations and input selectivity beyond average coherence generation, arXiv:2609.19046v1, PDF p. 7, Proposition 13, Second-order composition data

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P37

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- PDF p.7, Proposition 13: all second-order product invariants, including cross terms. -/
theorem secondOrderComposition [Nonempty ι] [Nonempty κ] (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup κ ℂ) :
    let m := (Fintype.card ι : ℝ)
    let n := (Fintype.card κ : ℝ)
    let A := response U
    let B := response V
    let G := response (Matrix.kronecker U V)
    G.trace = m * n - (m - A.trace) * (n - B.trace) ∧
    (G * G).trace = m * n - 2 * (m - A.trace) * (n - B.trace) +
      (m - 2 * A.trace + (A * A).trace) * (n - 2 * B.trace + (B * B).trace) ∧
    diagonalSq G = n * diagonalSq A + m * diagonalSq B + diagonalSq A * diagonalSq B +
      2 * A.trace * B.trace - 2 * diagonalSq A * B.trace - 2 * A.trace * diagonalSq B := by sorry

end QAlgorithms.Papers.Independent.Information100.P37

end
