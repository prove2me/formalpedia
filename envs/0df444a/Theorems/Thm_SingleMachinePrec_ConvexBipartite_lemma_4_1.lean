-- Prove2me | Theorems.Thm_SingleMachinePrec_ConvexBipartite_lemma_4_1
-- name    : SingleMachinePrec.ConvexBipartite.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:32:42.704388+00:00
-- url     : https://prove2.me/theorems/da06b2f3-67af-49b4-85f4-89322efe95af
-- title:
--   Lemma 4.1 — every convex bipartite order has a realizer of size 3
-- statement:
--   Let $\mathbf P = (N = J^- \cup J^+, P)$ be a convex bipartite order. Then $\mathbf P$ has a realizer of size $3$: there are linear extensions $L_1, L_2, L_3$ of $P$ such that every incomparable pair is reversed by one of them,
--   $$
--   \forall (x,y) \in \mathrm{inc}(\mathbf P)\ \ \exists m \in \{1,2,3\}:\ y <_{L_m} x .
--   $$
--   Consequently $\dim(\mathbf P) \le 3$: the class of convex bipartite orders has dimension at most $3$.
--
--   By Theorem 3.2 of the paper, a $3$-realizer of the precedence order yields a $4/3$-approximation for $1|\mathrm{prec}|\sum w_j C_j$ on convex bipartite instances.
--
--   **Formalization Note** The paper states: "Given a convex bipartite order $\mathbf P = (N,P)$, a realizer of size 3 can be computed in polynomial time." Its proof in the Appendix constructs the realizer explicitly; what is formalized is the existence of the realizer, which is the mathematical content of the lemma. The running-time claim is not formalized. The statement holds for every numbering of the plus jobs: no ordering assumption on $l$ is made.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 657, Lemma 4.1 (proof in the Appendix, pp. 667-668)

import Mathlib
import Definitions.Def_SingleMachinePrec_ConvexBipartite_ConvexBipartiteOrder

namespace SingleMachinePrec.ConvexBipartite

/-- Lemma 4.1 (Ambühl et al. 2011, p. 657), existence form. Every convex bipartite order has a
realizer of size 3: three linear extensions `L₁, L₂, L₃` of `P` such that every incomparable
pair is reversed by one of them. In particular its dimension is at most 3. -/
theorem lemma_4_1 {a b : ℕ} (C : ConvexBipartiteOrder a b) :
    ∃ L : Fin 3 → Job a b → Job a b → Prop, IsRealizer C.prec L := by sorry

end SingleMachinePrec.ConvexBipartite
