-- Prove2me | Theorems.Thm_TensorBTD_Gramian_partial_derivative_outer
-- name    : TensorBTD.Gramian.partial_derivative_outer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:15.533501+00:00
-- url     : https://prove2.me/theorems/8f5d8823-39ae-479a-9c0f-d36d0435a492
-- title:
--   Proof of Theorem 4.5, p. 12 — ∂ℱ/∂a^(n)_{i r} = a^(1)_r ∘ ⋯ ∘ e^(n)_i ∘ ⋯ ∘ a^(N)_r
-- statement:
--   Consider the canonical polyadic decomposition of an $N$-th order complex tensor $\mathcal T\in\mathbb C^{I_1\times\cdots\times I_N}$ in $R'$ rank-one terms, with factor matrices $A^{(n)} = [a^{(n)}_1\ \cdots\ a^{(n)}_{R'}]\in\mathbb C^{I_n\times R'}$ all treated as unknowns, and residual tensor
--   $$\mathcal F = \sum_{c=1}^{R'} a^{(1)}_c\circ\cdots\circ a^{(N)}_c - \mathcal T.$$
--   Let $e^{(n)}_i$ be the $i$-th column of the identity matrix $\mathbb I_{I_n}$. Then, for every mode $n$, column $r$ and row $i$, the partial (complex) derivative of the residual with respect to the entry $a^{(n)}_{ir}$ is the rank-one tensor
--   $$\frac{\partial\mathcal F}{\partial a^{(n)}_{ir}} = a^{(1)}_r\circ\cdots\circ a^{(n-1)}_r\circ e^{(n)}_i\circ a^{(n+1)}_r\circ\cdots\circ a^{(N)}_r .$$
--   In other words, the column of the Jacobian $\partial\,\mathrm{vec}(\mathcal F)/\partial x^{\mathrm T}$ belonging to the unknown $a^{(n)}_{ir}$ is the outer product of the $r$-th columns of all factor matrices, with the $n$-th one replaced by a unit vector. This holds for every tensor $\mathcal T$ and every choice of factor matrices.
--
--   This is the first display of the proof of Theorem 4.5; the inner products of these columns give all blocks of the Gramian.
--
--   **Formalization Note.** The unknowns $x$ are indexed by (mode, (column, row)); the CPD here is the unstructured one in $R'=\sum_r L_r$ terms of the mission's setting. The derivative is the complex derivative of $t\mapsto\mathcal F(x+te_\beta)$ at $0$. The identity is stated as an equality of tensors (functions of the multi-index), with the $n$-th vector replaced via `Function.update`.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), p. 12, proof of Theorem 4.5, first display

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Gramian

open Matrix

theorem partial_derivative_outer {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n)) :
    (fun ι => jac (cpdResidual T) x ι ⟨n, (r, i)⟩) =
      outer (Function.update (fun m k => cpdFactor x m k r) n (Pi.single i 1)) := by sorry

end TensorBTD.Gramian
