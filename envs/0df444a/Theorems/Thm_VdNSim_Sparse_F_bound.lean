-- Prove2me | Theorems.Thm_VdNSim_Sparse_F_bound
-- name    : VdNSim.Sparse.F_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:56.000303+00:00
-- url     : https://prove2.me/theorems/e6b62254-e860-49ad-91b1-283f33f0407c
-- title:
--   p. 12, after Eq. (7) — bound on the forward sampling function
-- statement:
--   Suppose the spectral norm of $A$ is at most one and $(\alpha_i,r_i)$ is column data for $A$. For arbitrary coefficient vectors $\psi$ and $\phi$, the function $F_i$ of Eq. (7) satisfies
--
--   $$|F_i(x)|\le1\qquad\text{for every }i,x.$$
--
--   This uniform bound lets the Chernoff–Hoeffding estimate apply to each forward sampled contribution.
--
--   **Formalization Note** The paper's efficiency assertion in the same sentence is outside the finite accuracy model; the inequality itself requires no normalization of either vector. The norm is the spectral operator norm, not a maximum-entry norm.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 12, sentence following Eq. (7)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Page 12, after Eq. (7): the importance-sampling summand is bounded by one. -/
theorem F_bound {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (hA : QAlgorithms.specNorm A ≤ 1)
    (D : ColumnData A s) (ψ ϕ : X → ℂ) (i : Fin s) (x : X) :
    ‖F ψ ϕ D i x‖ ≤ 1 := by sorry

end VdNSim.Sparse
