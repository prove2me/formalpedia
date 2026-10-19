-- Prove2me | Theorems.Thm_STVFriedmann_corollary1_order1_SM_eigenpairs
-- name    : STVFriedmann.corollary1_order1_SM_eigenpairs
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T01:56:17.109981+00:00
-- url     : https://prove2.me/theorems/be7601ad-b7d7-4ab9-89e7-8614c8eacec6
-- title:
--   STV ODE of order 1: eigenpairs of the saddle SM
-- statement:
--   Let $F_1(z_2,w_0) = \left(2z_2-3z_2w_0,\; -\tfrac16 z_2 + w_0 - w_0^2\right)$ be the right-hand side of the order-1 STV ODE (2.34)–(2.35), and let $DF_1(SM)$ be its Jacobian at the rest point $SM=(\tfrac43,\tfrac23)$. Then
--
--   $$
--   DF_1(SM)\begin{pmatrix}-9\\ 3/2\end{pmatrix} = \frac23\begin{pmatrix}-9\\ 3/2\end{pmatrix},\qquad
--   DF_1(SM)\begin{pmatrix}4\\ 1\end{pmatrix} = -\begin{pmatrix}4\\ 1\end{pmatrix}.
--   $$
--
--   So $SM$ is a saddle with unstable eigenvalue $\lambda_{A1}=\tfrac23$ and stable eigenvalue $\lambda_{B1}=-1$; the eigenvectors are the first two components of $\boldsymbol R_{A1}$ and $\boldsymbol R_{B1}$ in (2.30)–(2.31).
--
--   **Formalization Note** The Jacobian is Mathlib's Fréchet derivative `fderiv ℝ stvField1 restSM1`, applied to the vector.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, pp. 12-13, Corollary 1 eqs. (2.29)-(2.31) and the text following Figure 1's caption reference (first two components of R_A1, R_B1 are the eigenvectors of SM at n = 1)

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Corollary 1 (n = 1), (2.30)–(2.31) restricted to the first two components: the Jacobian
of the order-1 STV ODE at `SM` has eigenpairs `(2/3, (-9, 3/2))` and `(-1, (4, 1))`. -/
theorem corollary1_order1_SM_eigenpairs :
    fderiv ℝ stvField1 restSM1 ![-9, 3 / 2] = (2 / 3 : ℝ) • ![-9, 3 / 2] ∧
    fderiv ℝ stvField1 restSM1 ![4, 1] = (-1 : ℝ) • ![4, 1] := by sorry

end STVFriedmann
