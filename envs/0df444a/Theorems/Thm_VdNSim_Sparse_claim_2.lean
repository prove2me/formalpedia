-- Prove2me | Theorems.Thm_VdNSim_Sparse_claim_2
-- name    : VdNSim.Sparse.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:57.754987+00:00
-- url     : https://prove2.me/theorems/7d4ebe0d-9b21-4837-a013-48183e05e8fc
-- title:
--   Claim 2, p. 13 — bound on the reverse sampling function
-- statement:
--   Let $A$ be $s$-sparse with spectral norm at most one, and let $(\alpha_i,r_i)$ be column data for $A$. For arbitrary coefficient vectors $\psi$ and $\phi$, the function $G_i$ of Eq. (8) satisfies
--
--   $$|G_i(y)|\le s\qquad\text{for every }i,y.$$
--
--   This bound controls the second, reverse sampled part of the estimator in Theorem 3.
--
--   **Formalization Note** The row sparsity hypothesis bounds the number of summands; column data supplies the actual coefficients. Neither state needs normalization for this pointwise inequality.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 13, Claim 2

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Claim 2, p. 13: the reverse-sampled function has modulus at most s. -/
theorem claim_2 {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (hsp : IsSparse s A)
    (hA : QAlgorithms.specNorm A ≤ 1)
    (D : ColumnData A s) (ψ ϕ : X → ℂ) (i : Fin s) (y : X) :
    ‖G ψ ϕ D i y‖ ≤ (s : ℝ) := by sorry

end VdNSim.Sparse
