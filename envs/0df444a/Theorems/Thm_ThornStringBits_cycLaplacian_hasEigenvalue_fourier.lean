-- Prove2me | Theorems.Thm_ThornStringBits_cycLaplacian_hasEigenvalue_fourier
-- name    : ThornStringBits.cycLaplacian_hasEigenvalue_fourier
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:41:43.930901+00:00
-- url     : https://prove2.me/theorems/6dac2d4c-5b73-4518-9c72-6e3df206a475
-- title:
--   Each $4\sin^2(\pi k/M)$ is an eigenvalue of the cyclic Laplacian
-- statement:
--   Let $M\ge 1$ and let $k\in\mathbb N$. Then
--   $$ \lambda_k = 4\sin^2\!\Bigl(\frac{\pi k}{M}\Bigr) $$
--   is an eigenvalue of the cyclic Laplacian $L_M$ acting on $\mathbb R^M$: there is a nonzero $v\in\mathbb R^M$ with $L_Mv=\lambda_k v$.
--
--   These are the normal-mode eigenvalues of the discretized light-cone string of Thorn's p. 4 Hamiltonian; the mode of wave number $k$ oscillates with angular frequency $\sqrt{\lambda_k}/\epsilon=(2/\epsilon)|\sin(\pi k/M)|$.
--
--   **Formalization Note** The eigenvalue is taken for the real linear map $x\mapsto L_Mx$, so a real eigenvector is required.
-- source:
--   C. B. Thorn, *Reformulating String Theory with the 1/N Expansion*, arXiv:hep-th/9405069v1 (1994; talk at the First Int. A. D. Sakharov Conf., 1991), https://arxiv.org/abs/hep-th/9405069, pp. 4–5.

import Definitions.Def_ThornStringBits_Defs
import Mathlib

open Real Matrix

namespace ThornStringBits

theorem cycLaplacian_hasEigenvalue_fourier (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M))
      (4 * Real.sin (π * k / M) ^ 2) := by sorry

end ThornStringBits
