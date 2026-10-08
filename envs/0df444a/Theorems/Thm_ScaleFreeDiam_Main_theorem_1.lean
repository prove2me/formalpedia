-- Prove2me | Theorems.Thm_ScaleFreeDiam_Main_theorem_1
-- name    : ScaleFreeDiam.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:09.015092+00:00
-- url     : https://prove2.me/theorems/dc617862-d3dd-40a2-9123-371c9903d26a
-- title:
--   Theorem 1, p. 9 — for m ≥ 2, a.e. G_mⁿ is connected with (1−ε) log n/log log n ≤ diam(G_mⁿ) ≤ (1+ε) log n/log log n
-- statement:
--   Fix an integer $m\ge2$ and a real number $\varepsilon>0$. Let $G_m^n$ be the random graph on $[n]$ obtained from the preferential-attachment process $G_1^{mn}$ by identifying the vertices in consecutive groups of $m$. Then almost every $G_m^n\in\mathcal G_m^n$ is connected and has diameter satisfying
--   $$
--   (1-\varepsilon)\frac{\log n}{\log\log n}\le\operatorname{diam}(G_m^n)\le(1+\varepsilon)\frac{\log n}{\log\log n},
--   $$
--   that is, the probability of this event tends to $1$ as $n\to\infty$ with $m$ fixed. Logarithms are natural.
--
--   This is the main result of the paper: the Barabási–Albert scale-free graph with $m\ge2$ edges per vertex has diameter asymptotically $\log n/\log\log n$, smaller than the order $\log n$ of the diameter of a classical random graph with the same fixed average degree.
--
--   **Formalization Note** The diameter is Mathlib's `SimpleGraph.diam` of the simple-graph shadow of $G_m^n$; it is $0$ for a disconnected graph, which is why connectivity is part of the event, as on the page.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 9, Theorem 1

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process

namespace ScaleFreeDiam.Main

open Filter Topology MeasureTheory ProbabilityTheory
open scoped Classical

theorem theorem_1 (m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    AlmostEvery m (fun n G => G.Connected ∧
      (1 - ε) * Real.log n / Real.log (Real.log n) ≤ (G.diam : ℝ) ∧
      (G.diam : ℝ) ≤ (1 + ε) * Real.log n / Real.log (Real.log n)) := by sorry

end ScaleFreeDiam.Main
