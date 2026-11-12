-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_2
-- name    : SubcubicBA.PlainPKI.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:12.097194+00:00
-- url     : https://prove2.me/theorems/2524b20e-4bb5-4c91-b992-f408dc15a533
-- title:
--   Theorem 2 — explicit fault-tolerant expanders
-- statement:
--   For every $\alpha\in(0,1)$ and $\beta>1$ there are constants $D>0$ and $c$ and an explicit family of graphs $G_n$ on $n$ vertices ($n>0$), each of maximum degree at most $D$, with the following property: for every set $C$ of vertices with $|C|\le\alpha n$ there is a set $S$ disjoint from $C$ with
--   $$|S|\ge n-\beta|C|$$
--   such that the induced subgraph $G_n[S]$ is connected and any two vertices of $S$ are at distance at most $c\log_2 n$ in $G_n[S]$. Explicit means that $n\mapsto G_n$ (with $n$ in unary and output the adjacency bit matrix) is computed in polynomial time.
--
--   The theorem generalizes Upfal's construction ($\alpha=1/72$, $\beta=6$) to all $\alpha,\beta$; in SpreadVotes it gives $4n/10$ honest parties that reach one another in $O(\log n)$ rounds.
--
--   Differences from the source:
--   - encoding: explicit: constructed deterministically in polynomial time (p. 37) → one function from the parameters in unary to the adjacency bit matrix, computed by a Turing machine in polynomial time (TM2ComputableInPolyTime); reason: the paper's definition of explicit; unary parameters make the time polynomial in n
--   - encoding: diameter O(log n) → a constant c chosen with D before n, and distance at most c·log₂ n between any two vertices of S in G[S]; reason: the definition of O(·) uniform in n
--   - encoding: bounded degree D on n vertices → a symmetric loopless n × n bit matrix with at most D ones per row, D > 0; reason: same graphs
--   - encoding: G[S] connected → Mathlib's Connected, which requires S nonempty; reason: a vertex outside C always exists (|C| ≤ αn < n), so a singleton S is available whenever the source's bound allows a small S
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 2, p. 39 (first stated p. 5)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Graphs

namespace SubcubicBA.PlainPKI

/-- Theorem 2 (p. 39; first stated p. 5). -/
theorem theorem_2 (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : 1 < β) :
    ∃ D : ℕ, 0 < D ∧ ∃ cdiam : ℝ, ∃ f : ℕ → List Bool, PolyTimeFamily unary1 f ∧
      ∀ n : ℕ, 0 < n →
        IsSimpleAdjBits (f n) n ∧
        (∀ u : Fin n, (nbhdOfBits (f n) n n u).card ≤ D) ∧
        FaultTolerant (graphOfBits (f n) n) α β (cdiam * Real.logb 2 n) := by sorry

end SubcubicBA.PlainPKI
