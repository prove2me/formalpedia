-- Prove2me | Theorems.Thm_ResistanceRigidity_AverageLaw_theorem_3_1
-- name    : ResistanceRigidity.AverageLaw.theorem_3_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T23:06:35.143813+00:00
-- url     : https://prove2.me/theorems/6365f4dd-b0b3-4962-81b3-a0965d241db6
-- title:
--   Theorem 3.1 (the average law) — $\varepsilon \ge (N-1-d)/((N-1)(d-1))$, with equality exactly for complete, triangle-free strongly regular and star graphs
-- statement:
--   Let $G$ be a connected weighted graph on a finite vertex set $V$ with $N \ge 3$ vertices, given by its conductance function $c$ (symmetric, nonnegative, zero on the diagonal; the edges are the pairs with $c > 0$). Let $m$ be its number of edges, $d = 2m/N$ its average support degree, $R_{uv}$ its effective resistances and
--   $$\varepsilon = \frac{\max_{u\ne v} R_{uv}}{\min_{u\ne v} R_{uv}} - 1$$
--   its spread. Then
--   $$\varepsilon \;\ge\; \frac{N - 1 - d}{(N-1)(d-1)} . \tag{6}$$
--   Equality holds if and only if, up to scaling, $G$ has equal conductances (some $w > 0$ is the conductance of every edge) and belongs to one of three classes: the complete graphs, the connected non-complete triangle-free strongly regular graphs, and the stars $K_{1,N-1}$. Moreover, with equal conductances, a complete graph has $\varepsilon = 0$, a connected non-complete triangle-free strongly regular graph has $0 < \varepsilon < 1$, and a star has $\varepsilon = 1$.
--
--   This is the average law of the paper: a graph whose effective resistances are all within a factor $1 + \varepsilon$ of each other must have average degree close to $N - 1$, and the bound is attained exactly by the three listed families. It gives a lower bound on the number of edges of any graph whose resistances approximate those of the complete graph, which is the edge barrier for resistance sparsifiers of $K_N$.
--
--   Differences from the source:
--   - encoding: a graph with positive edge conductances $w$, $w_{uv} = 0$ off the edges and on the diagonal → a conductance function $c : V \to V \to \mathbb R$ that is symmetric, nonnegative and zero on the diagonal, edges being the pairs with $c > 0$; reason: the same weighted graphs.
--   - encoding: "up to scaling, $G$ has equal conductances" → there is $w > 0$ with $c(u,v) = w$ on every edge; reason: scaling is exactly the freedom in $w$.
--   - reading: the parenthetical values "(ε = 0)", "(0 < ε < 1)", "(ε = 1)" attached to the three classes → for every graph with equal conductances in the class, $\varepsilon$ has that value; reason: the proof establishes each value for every member of its class ("Conversely, such a graph has ε = 0", "such a star has ε = 1", and the strongly regular computation $\varepsilon = 1/(k + \mu - 1)$); this is the stronger of the possible readings.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 6, §3, Theorem 3.1, eq. (6)

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Spread
import Definitions.Def_ResistanceRigidity_AverageLaw_Classes

namespace ResistanceRigidity.AverageLaw

/-- Theorem 3.1 (the average law): a connected weighted graph on `N ≥ 3` vertices with `m` edges
and `d = 2m/N` has spread `ε ≥ (N − 1 − d)/((N − 1)(d − 1))`; equality holds if and only if,
up to scaling, the conductances are equal and the graph is complete, connected non-complete
triangle-free strongly regular, or a star; and with equal conductances these classes have
`ε = 0`, `0 < ε < 1` and `ε = 1` respectively. -/
theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 3 ≤ Fintype.card V) :
    ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) ≤
        spread c ∧
      (spread c =
          ((Fintype.card V : ℝ) - 1 - avgDeg c) / (((Fintype.card V : ℝ) - 1) * (avgDeg c - 1)) ↔
        EqualConductances c ∧ (IsComplete c ∨ IsTriangleFreeSRG c ∨ IsStar c)) ∧
      (EqualConductances c → IsComplete c → spread c = 0) ∧
      (EqualConductances c → IsTriangleFreeSRG c → 0 < spread c ∧ spread c < 1) ∧
      (EqualConductances c → IsStar c → spread c = 1) := by sorry

end ResistanceRigidity.AverageLaw
