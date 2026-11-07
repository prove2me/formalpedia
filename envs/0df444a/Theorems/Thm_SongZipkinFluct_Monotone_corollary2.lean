-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_corollary2
-- name    : SongZipkinFluct.Monotone.corollary2
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T12:55:22.201218+00:00
-- url     : https://prove2.me/theorems/f10c9d28-3d34-4aa5-ae2f-7e3cf9ef73d7
-- title:
--   Corollary 2: the finite-horizon basestock levels $y^*_n(i)$ converge as $n\to\infty$
-- statement:
--   Assume the standing hypotheses of the model and Assumption 1 ($\alpha\bar c<p$), in the linear-cost model ($K=0$, $W_0\equiv0$). Let $y^*_n(i)$, $n\ge1$, be the smallest minimizer of $G_n(i,\cdot)$ (recursion (13)). Then for every world state $i$ the integer sequence $(y^*_n(i))_n$ converges, i.e. $y^*_\infty(i)=\lim_{n\to\infty}y^*_n(i)$ exists.
--
--   In the paper this follows from Theorem 1 (printed "Theorem 4"), p. 357: $y^*_n(i)$ is nonincreasing in $n$ and bounded below by $y^+_{\min}$, so it is eventually constant (Corollary 2, p. 357). The statement is phrased for every choice of the minimizers $y^*_n(i)$ for $n\ge1$; the value at $n=0$ is irrelevant to the limit.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Corollary 2 (and Theorem 1 (printed "Theorem 4") (f)–(g))

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Recursion

open Filter Topology

namespace SongZipkinFluct.Monotone

theorem corollary2 {I : Type} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) :
    ∀ ys : ℕ → I → ℤ, (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) →
      ∀ i, ∃ y : ℤ, Tendsto (fun n => ys n i) atTop (𝓝 y) := by sorry

end SongZipkinFluct.Monotone
