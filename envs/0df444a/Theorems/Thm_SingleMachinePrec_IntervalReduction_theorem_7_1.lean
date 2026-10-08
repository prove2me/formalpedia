-- Prove2me | Theorems.Thm_SingleMachinePrec_IntervalReduction_theorem_7_1
-- name    : SingleMachinePrec.IntervalReduction.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:32:18.888813+00:00
-- url     : https://prove2.me/theorems/cdff96cf-40a5-43ec-894c-5c189c8edfe3
-- title:
--   Theorem 7.1 — vertex cover on connected graphs of degree at most 3 reduces to $1|\mathrm{prec}|\sum w_jC_j$ on interval orders
-- statement:
--   The paper states: *Problem $1|\mathrm{prec}|\sum w_jC_j$ with precedence constraints that form an interval order is NP-hard.* Its proof reduces vertex cover on connected graphs of maximum degree 3, which is NP-complete (Garey, Johnson and Stockmeyer). What the proof establishes, and what is formalized, is the correctness of that reduction.
--
--   Let $G=(V,E)$ be a connected graph in which every vertex has at most $3$ neighbours, let $T=(V,E_T)$ be a spanning tree of $G$ rooted at $v_1$ whose numbering puts every parent before its children, and let $m\ge 0$ be an integer. Let $S$ be the scheduling instance of Stage 2 built from $G$ and $T$, with $n$ jobs and $k=n^2+1$, let $I$ be its precedence constraints and $w(C_I)$ the minimum weight of a vertex cover of $G^S_I$. Set $c=|V|+|E\setminus E_T|$. Then
--
--   1. $I$ is an interval order, and
--   2. $G$ has a vertex cover of size at most $m$ if and only if
--   $$\lfloor w(C_I)\rfloor \le m + c.$$
--
--   Since solving $S$ is equivalent to finding a minimum weight vertex cover of $G^S_I$ (Theorem 2.1 of the paper), this shows that $1|\mathrm{prec}|\sum w_jC_j$ remains hard when the precedence constraints form an interval order, a class on which many scheduling problems become polynomially solvable.
--
--   **Formalization Note** "NP-hard", the NP-completeness of the source problem, and the polynomial size of the construction are not formalized. Neither is the passage from $G^S_I$ to schedules (Theorem 2.1, cited). The statement holds for every parent-first spanning tree, not only the paper's breadth-first tree. The connectivity and degree hypotheses are kept as in the paper, although the reduction's correctness does not use them. The interval order is `AppliedComb.Posets.IsIntervalOrder` applied to the instance's order on jobs; $\lfloor\cdot\rfloor$ is `Nat.floor` ($w(C_I)\ge 0$).
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 661, Theorem 7.1 (proof pp. 661–664, equation (9))

import Mathlib
import Definitions.Def_AppliedComb_Posets_intervalOrder
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Theorem 7.1 (p. 661), in the form its proof (pp. 661–664) establishes: for a connected graph
`G` of maximum degree at most 3 with a rooted spanning tree numbered parent-first, the instance
`S` of Stage 2 (with `k = n² + 1`) has interval-order precedence constraints, and `G` has a vertex
cover of size at most `m` if and only if `⌊w(C_I)⌋ ≤ m + c`, where `c = |V| + |E \ E_T|`. -/
theorem theorem_7_1 {N : ℕ} (G : SimpleGraph (Fin N)) (hconn : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 3) (L : TreeLayout G) (m : ℕ) :
    AppliedComb.Posets.IsIntervalOrder (Job L) ∧
    ((∃ C : Finset (Fin N), G.IsVertexCover (C : Set (Fin N)) ∧ C.card ≤ m) ↔
      ⌊tauW L⌋₊ ≤ m + N + Fintype.card (NonTreeEdge L)) := by sorry

end SingleMachinePrec.IntervalReduction
