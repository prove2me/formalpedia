-- Prove2me | Theorems.Thm_RevConvexDisj_MultiTerm_theorem_5
-- name    : RevConvexDisj.MultiTerm.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:05.516294+00:00
-- url     : https://prove2.me/theorems/f9bb551f-4696-4343-b262-c3fbd726d571
-- title:
--   Theorem 5, p. 17 — P^B \ T^C is the union of P^B \ S^C_k over k ∈ N2 ∪ {0}
-- statement:
--   Let $A\in\mathbb{R}^{m\times n}$ have full row rank, $b\in\mathbb{R}^m$, and fix a basis $B$ of $Ax=b$ with nonbasic set $N$, basic solution $\bar x$, basis cone $P^B$ and extreme rays $\bar r^j$ ($j\in N$). Let $C\subseteq\mathbb{R}^n$ be open and convex with $\bar x\notin\operatorname{cl}(C)$, and assume (Assumption 2) that the recession cone of $C$ is contained in that of $P^B$. With $\alpha_j,\beta_j$, the partition $N_0,N_1,N_2$ of $N$, $N_0^{\mathrm c}=N_1\cup N_2$, the inner approximation $T^C$ of (7) and the sets $S^C_0$ of (26) and $S^C_k$ ($k\in N_2$) of (27), and with $N_2^0 := N_2\cup\{0\}$,
--   $$P^B\setminus T^C = \bigcup_{k\in N_2^0}\big(P^B\setminus S^C_k\big)\qquad (31).$$
--
--   The set $P^B\setminus T^C$ is a relaxation of the reverse convex set $P^B\setminus C$ that retains its closed convex hull. Theorem 5 expresses it as a disjunction of $|N_2|+1$ terms, each the complement in $P^B$ of a set with explicit structure; this disjunction generalizes the two-term intersection disjunction of the paper's Theorem 1 by exploiting the full recession cone of $C$, and is the starting point for the paper's polyhedral relaxations of the terms and cut generation by disjunctive programming.
--
--   **Formalization Note.** The term "$k=0$" is $P^B\setminus S^C_0$ and the others are $P^B\setminus S^C_k$ for $k\in N_2$. The hypotheses are the paper's standing assumptions: openness and convexity of $C$ and full row rank (§2), $\bar x\notin\operatorname{cl}(C)$ (§3), Assumption 2 (stated for all of §4). The basic solution is not assumed feasible ($\bar b\ge 0$ is not imposed).
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 17, Theorem 5, (31)

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

namespace RevConvexDisj.MultiTerm

theorem theorem_5 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : BasisData ι) (C : Set (ι → ℝ))
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hxbar : D.xbar ∉ closure C)
    (hA2 : recc C ⊆ recc D.PB) :
    D.PB \ TC D C = (D.PB \ SC0 D C) ∪ ⋃ k ∈ N2 D C, (D.PB \ SCk D C k) := by sorry

end RevConvexDisj.MultiTerm
