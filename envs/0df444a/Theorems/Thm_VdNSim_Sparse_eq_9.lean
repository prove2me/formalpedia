-- Prove2me | Theorems.Thm_VdNSim_Sparse_eq_9
-- name    : VdNSim.Sparse.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:57.058034+00:00
-- url     : https://prove2.me/theorems/28a68c22-b815-4739-b7a4-f45033f0c6ec
-- title:
--   Eq. (9), p. 13 — at most s column preimages of a row
-- statement:
--   Let $A$ have at most $s$ nonzero entries in each row and column, with column data $(\alpha_j,r_j)_{j=1}^{s}$. For any row $y$, at most $s$ columns $x$ have $r_j(x)=y$ and $\alpha_j(x)\ne0$ for some $j$. Consequently, for each fixed $i$ there are also at most $s$ such $x$ in slot $i$:
--
--   $$\#\{x:\exists j,\ r_j(x)=y,\ \alpha_j(x)\ne0\}\le s,\qquad\#\{x:r_i(x)=y,\ \alpha_i(x)\ne0\}\le s.$$
--
--   This count is the finite content of the row-access argument used in Claim 2.
--
--   **Formalization Note** The paper additionally asserts efficient enumeration of these preimages. Running time is not represented here.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 13, Eq. (9) and following sentence

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Equation (9): every row has at most s columns represented by nonzero column data. -/
theorem eq_9 {X : Type*} [Fintype X] [DecidableEq X]
    {A : Matrix X X ℂ} {s : ℕ} (hsp : IsSparse s A)
    (D : ColumnData A s) (y : X) :
    ((Finset.univ.filter fun x =>
      ∃ j : Fin s, D.r j x = y ∧ D.α j x ≠ 0).card ≤ s) ∧
    (∀ i : Fin s,
      (Finset.univ.filter fun x => D.r i x = y ∧ D.α i x ≠ 0).card ≤ s) := by sorry

end VdNSim.Sparse
