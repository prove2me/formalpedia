-- Prove2me | Theorems.Thm_TalagrandConc_BinPacking_theorem_6_5
-- name    : TalagrandConc.BinPacking.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:55.85871+00:00
-- url     : https://prove2.me/theorems/4a9f1b08-bcd3-44d2-8c92-2abf137dae69
-- title:
--   Theorem 6.5 — P(|B_N − M| ≥ 1 + u) ≤ 8 exp(−u²/(64 N E X₁²)) for 0 ≤ u ≤ 8√2 N E X₁²
-- statement:
--   Let $X_1,\dots,X_N$ be independent items with common law $\mu$ on $[0,1]$, realised as the coordinates of $[0,1]^N$ under the product probability $P = \mu^{\otimes N}$, and let $B_N(X_1,\dots,X_N)$ be the minimum number of unit bins into which they can be packed. Write $\mathbb E X_1^2 = \int \omega^2\,d\mu(\omega)$, and let $M$ be any median of $B_N$, i.e. $P(B_N \le M) \ge 1/2$ and $P(B_N \ge M) \ge 1/2$. Then for all $u$ with $0 \le u \le 8\sqrt 2\, N\,\mathbb E X_1^2$,
--   $$P\big(|B_N(X_1,\dots,X_N) - M| \ge 1 + u\big) \le 8\exp\Big(-\frac{u^2}{64\,N\,\mathbb E X_1^2}\Big).$$
--
--   The variance proxy in the exponent is $N\,\mathbb E X_1^2$ rather than $N$, which is the scale one expects when items are small, and improves on the martingale bound $2\exp(-2t^2/N)$.
--
--   **Formalization Note** The paper writes "for all $u \le 8\sqrt2 N E X_1^2$"; the restriction $u \ge 0$ is implicit (its proof sets $u = 4t\sqrt N (E X_1^2)^{1/2}$ with $t>0$) and is stated explicitly. When $N\,\mathbb E X_1^2 = 0$ the range forces $u = 0$, and Lean's convention $u^2/0 = 0$ makes the bound $8$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 152, Theorem 6.5

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

open MeasureTheory

/-- Talagrand (1995), p. 152, Theorem 6.5: if `M` is a median of `B_N` under the product
probability `P = μ^{⊗N}` on `[0,1]^N`, then for all `0 ≤ u ≤ 8 √2 N E X₁²`,
`P(|B_N(X₁, …, X_N) − M| ≥ 1 + u) ≤ 8 exp(−u² / (64 N E X₁²))`.
(The paper writes "for all `u ≤ 8√2 N E X₁²`"; `u ≥ 0` is implicit — its proof sets
`u = 4t √N (E X₁²)^{1/2}` with `t > 0` — and is stated here.) -/
theorem theorem_6_5 (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) (M : ℝ)
    (hM : IsMedian (Measure.pi (fun _ : Fin N => μ)) (fun x => (binNumber x : ℝ)) M)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 8 * Real.sqrt 2 * N * secondMoment μ) :
    Measure.pi (fun _ : Fin N => μ) {x | 1 + u ≤ |(binNumber x : ℝ) - M|} ≤
      ENNReal.ofReal (8 * Real.exp (-(u ^ 2 / (64 * N * secondMoment μ)))) := by sorry

end TalagrandConc.BinPacking
