-- Prove2me | Theorems.Thm_VdNSim_Sparse_eq_5
-- name    : VdNSim.Sparse.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:02.375507+00:00
-- url     : https://prove2.me/theorems/16a7172d-6b25-414e-8cac-42a3a3037c49
-- title:
--   Eq. (5), p. 12 — matrix element as a sum over sparse columns
-- statement:
--   Let $(\alpha_i,r_i)_{i=1}^{s}$ be column data for an operator $A$ on a finite computational basis. For coefficient vectors $\psi$ and $\phi$, put $\sigma_i=\sum_x\alpha_i(x)\overline{\phi_{r_i(x)}}\psi_x$. Then
--
--   $$\langle\phi|A|\psi\rangle=\sum_{i=1}^{s}\sigma_i.$$
--
--   This identity reorganizes a sparse matrix element into one contribution per column-data slot.
--
--   **Formalization Note** The displayed upper limit $n$ in the paper's first sentence before Eq. (5) is a printing error; the immediately following sentence says there are $s$ quantities $\sigma_i$. Lean uses $s$.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 12, Eq. (5)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Equation (5), with the paper's printed upper limit n corrected to s. -/
theorem eq_5 {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (D : ColumnData A s) (ψ ϕ : X → ℂ) :
    matElem ϕ A ψ =
      ∑ i : Fin s, ∑ x, D.α i x * star (ϕ (D.r i x)) * ψ x := by sorry

end VdNSim.Sparse
