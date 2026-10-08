-- Prove2me | Theorems.Thm_TalagrandConc_Assignment_theorem_10_5
-- name    : TalagrandConc.Assignment.theorem_10_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:11.084993+00:00
-- url     : https://prove2.me/theorems/0256726f-4480-461c-91e6-dce81086adf6
-- title:
--   Theorem 10.5 — concentration of the random assignment cost L_N around its median
-- statement:
--   Let the costs $X_{i,j}$, $i \in I$, $j \in J$, $|I| = |J| = N$, be independent and uniformly distributed on $[0,1]$, and let
--   $$L_N = \min\Big\{ \sum_{i \in I} X_{i,\tau(i)} \;;\; \tau : I \to J \text{ one-to-one} \Big\}$$
--   be the optimal assignment cost. There is a universal constant $K > 0$ such that for every $N \ge 3$, every median $M$ of $L_N$ and every $t \ge 0$:
--   $$t \le \sqrt{\log N} \Rightarrow P\Big(|L_N - M| \ge \frac{K t (\log N)^2}{\sqrt N \log\log N}\Big) \le 2\exp(-t^2), \tag{10.7}$$
--   $$t \ge \sqrt{\log N} \Rightarrow P\Big(|L_N - M| \ge \frac{K t^3 \log N}{\sqrt N \log t^2}\Big) \le 2\exp(-t^2). \tag{10.8}$$
--
--   Since $E(L_N)$ stays bounded as $N \to \infty$, this shows that the fluctuations of $L_N$ are at most of order $(\log N)^2/(\sqrt N \log\log N)$, much smaller than its mean.
--
--   **Formalization Note** One constant $K$ serves both (10.7) and (10.8) and is chosen before $N$, $M$ and $t$. A median is any $M$ with $P(L_N \le M) \ge 1/2$ and $P(L_N \ge M) \ge 1/2$. The paper leaves $t \ge 0$ implicit; for negative $t$ (10.7) would fail. For $N \ge 3$, $\log\log N > 0$, and $t \ge \sqrt{\log N} > 1$ gives $\log t^2 > 0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 169, Theorem 10.5, Eqs. (10.7)–(10.8)

import Mathlib
import Definitions.Def_TalagrandConc_Assignment_Basic

namespace TalagrandConc.Assignment

open MeasureTheory

/-- Talagrand (1995), p. 169, Theorem 10.5. There is a universal constant `K > 0` such that
for every `N ≥ 3`, every median `M` of the optimal assignment cost `L_N` (costs i.i.d.
uniform on `[0, 1]`) and every `t ≥ 0`:
(10.7) if `t ≤ √(log N)` then `P(|L_N − M| ≥ K t (log N)² / (√N log log N)) ≤ 2 exp(−t²)`;
(10.8) if `t ≥ √(log N)` then `P(|L_N − M| ≥ K t³ log N / (√N log t²)) ≤ 2 exp(−t²)`. -/
theorem theorem_10_5 :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 3 ≤ N → ∀ M : ℝ, TalagrandConc.BinPacking.IsMedian (costLaw N) optCost M →
      ∀ t : ℝ, 0 ≤ t →
        (t ≤ Real.sqrt (Real.log N) →
          costLaw N {X | K * t * Real.log N ^ 2 / (Real.sqrt N * Real.log (Real.log N)) ≤
              |optCost X - M|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2))) ∧
        (Real.sqrt (Real.log N) ≤ t →
          costLaw N {X | K * t ^ 3 * Real.log N / (Real.sqrt N * Real.log (t ^ 2)) ≤
              |optCost X - M|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2))) := by sorry

end TalagrandConc.Assignment
