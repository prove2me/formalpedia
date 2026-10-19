-- Prove2me | Theorems.Thm_STVFriedmann_eigenvalues_SM_every_order
-- name    : STVFriedmann.eigenvalues_SM_every_order
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T01:58:53.784168+00:00
-- url     : https://prove2.me/theorems/22fa2a6a-e965-49e0-a5eb-bccd018f2e17
-- title:
--   Eigenvalues of SM at every order: 2k/3 and (2k-5)/3
-- statement:
--   For $k\ge1$ and $\boldsymbol v_1=(z_2,w_0)$, let
--
--   $$
--   P_k(\boldsymbol v_1)=\begin{pmatrix}(2k+1)(1-w_0)-1 & -(2k+1)z_2\\[2pt] -\dfrac{1}{2(2k+1)} & 2k(1-w_0)-1\end{pmatrix}
--   $$
--
--   be the diagonal block of the order-$n$ STV ODE in Theorem 3, eq. (2.26). At the critical Friedmann values $\boldsymbol v_1=(\tfrac43,\tfrac23)$ its characteristic polynomial is
--
--   $$
--   \det\bigl(X\,I-P_k(\tfrac43,\tfrac23)\bigr)=\Bigl(X-\frac{2k}{3}\Bigr)\Bigl(X-\frac{2k-5}{3}\Bigr),
--   $$
--
--   so its eigenvalues are $\lambda_{Ak}=\tfrac{2k}{3}$ and $\lambda_{Bk}=\tfrac13(2k-5)$.
--
--   By the block-triangular ("nested") structure (2.25) of the STV ODE, these are the eigenvalues of $SM$ that newly appear at order $k$.
--
--   **Formalization Note** The hypothesis $k\ge1$ matches the range of $k$ in the source; the matrix identity itself does not use it.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 11, Theorem 3 eq. (2.26); p. 12, Corollary 1 eq. (2.29); p. 19, Section 2.8

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Corollary 1, (2.29) computed from (2.26): for every `k ≥ 1`, the block `P_k(v₁)` at the
`SM` values `v₁ = (4/3, 2/3)` has characteristic polynomial `(X - 2k/3)(X - (2k-5)/3)`. -/
theorem eigenvalues_SM_every_order (k : ℕ) (hk : 1 ≤ k) :
    (stvBlockP k restSM1).charpoly =
      (Polynomial.X - Polynomial.C (2 * (k : ℝ) / 3)) *
        (Polynomial.X - Polynomial.C ((2 * (k : ℝ) - 5) / 3)) := by sorry

end STVFriedmann
