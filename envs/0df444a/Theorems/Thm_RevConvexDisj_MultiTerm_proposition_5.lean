-- Prove2me | Theorems.Thm_RevConvexDisj_MultiTerm_proposition_5
-- name    : RevConvexDisj.MultiTerm.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:19.017994+00:00
-- url     : https://prove2.me/theorems/c5f67f0a-98b7-41c6-92c0-c79df99634c0
-- title:
--   Proposition 5, p. 17 — S^C_k = {x̄} + conv(⋃_{j∈N^c_0} (α_j, β_j) r̄^j) + (−∞, 0] r̄^k + recc(C)
-- statement:
--   Let $C\subseteq\mathbb{R}^n$ be open and convex, let $\bar x\notin\operatorname{cl}(C)$ be a basic solution with basis cone $P^B$, extreme rays $\bar r^j$ and parameters $\alpha_j,\beta_j$ ($j\in N$), and assume (Assumption 2) $\operatorname{recc}(C)\subseteq\operatorname{recc}(P^B)$. For $k\in N_2$, the disjunctive term
--   $$S^C_k = \{\bar x\} + \operatorname{conv}\Big(\bigcup_{j\in N_2}[0,\beta_j)\bar r^j\Big) + (-\infty,0]\bar r^k + \operatorname{recc}(C)$$
--   can equivalently be written as
--   $$S^C_k = \{\bar x\} + \operatorname{conv}\Big(\bigcup_{j\in N_0^{\mathrm c}}(\alpha_j,\beta_j)\bar r^j\Big) + (-\infty,0]\bar r^k + \operatorname{recc}(C)\qquad (28),$$
--   where $N_0^{\mathrm c} = N_1\cup N_2$.
--
--   The second form makes visible that $S^C_k$ contains $T^C$, and it is the representation of $S^C_k$ used in the proof of Theorem 5.
--
--   **Formalization Note.** $\bar x\notin\operatorname{cl}(C)$ and Assumption 2 are the paper's standing assumptions for §4 and are kept as hypotheses although the paper's argument does not invoke them.
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 17, Proposition 5, (28)

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

namespace RevConvexDisj.MultiTerm

open scoped Pointwise

theorem proposition_5 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : BasisData ι) (C : Set (ι → ℝ))
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hxbar : D.xbar ∉ closure C)
    (hA2 : recc C ⊆ recc D.PB) :
    ∀ k ∈ N2 D C, SCk D C k =
      {D.xbar} + convexHull ℝ (⋃ j ∈ N0c D C, openSeg (alpha D C j) (beta D C j) (D.ray j))
        + nonposRay (D.ray k) + recc C := by sorry

end RevConvexDisj.MultiTerm
