-- Prove2me | Theorems.Thm_RevConvexDisj_MultiTerm_observation_N1_recc
-- name    : RevConvexDisj.MultiTerm.observation_N1_recc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:07.280298+00:00
-- url     : https://prove2.me/theorems/5a1b8843-9c8b-4744-b2c2-8f73b3f99173
-- title:
--   §3, p. 5 — for j ∈ N1 the extreme ray r̄^j is a recession direction of C
-- statement:
--   Let $C\subseteq\mathbb{R}^n$ be open and convex, and let $\bar x$ be a basic solution with basis cone $P^B$ and extreme rays $\bar r^j$ ($j\in N$) such that $\bar x\notin\operatorname{cl}(C)$. Let $N_1$ be the set of nonbasic indices $j$ with $\alpha_j\in(0,+\infty)$ and $\beta_j=+\infty$, i.e. the halfline from $\bar x$ in direction $\bar r^j$ enters $C$ and never leaves it. Then
--   $$\bar r^j\in\operatorname{recc}(C)\qquad\text{for every } j\in N_1.$$
--
--   This observation is what lets the segments $(\alpha_j,\beta_j)\bar r^j$, $j\in N_1$, be absorbed into $\operatorname{recc}(C)$ in the proof of Proposition 5.
--
--   **Formalization Note.** $\operatorname{recc}(C) = \{d : x+td\in C\ \forall x\in C,\ t\ge 0\}$; openness of $C$ is used to pass from one halfline inside $C$ to every point of $C$. The hypothesis $\bar x\notin\operatorname{cl}(C)$ is the paper's standing assumption for §3 onward.
-- source:
--   Towle & Luedtke, Intersection disjunctions for reverse convex sets, arXiv:1901.02112v5, p. 5, §3, "Observe r̄^j ∈ recc(C) for j ∈ N1"

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

namespace RevConvexDisj.MultiTerm

theorem observation_N1_recc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : BasisData ι) (C : Set (ι → ℝ))
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hxbar : D.xbar ∉ closure C) :
    ∀ j ∈ N1 D C, D.ray j ∈ recc C := by sorry

end RevConvexDisj.MultiTerm
