-- Prove2me | Theorems.Thm_VeinottNoDiscount_Overtake_display_27
-- name    : VeinottNoDiscount.Overtake.display_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:22.329008+00:00
-- url     : https://prove2.me/theorems/e71e7dbf-07c3-41a5-9de4-443fa5d3859c
-- title:
--   (27) — y(f) = lim_{N→∞} N⁻¹ Σ_{n=1}^N [Vⁿ(f^∞) − nx(f)]
-- statement:
--   Let $f\in F$ be a decision rule with gain $x(f)$ and bias $y(f)$, and let $V^n(f^\infty)$ be the vector of total expected returns in the first $n$ periods under the stationary policy $f^\infty$. Then
--   $$y(f)=\lim_{N\to\infty}\frac1N\sum_{n=1}^{N}\bigl[V^n(f^\infty)-n\,x(f)\bigr],$$
--   the limit taken coordinatewise.
--
--   Thus $[y(f)]_s$ is the average amount by which the total expected return for $n$ periods starting from state $s$ exceeds that starting from the stationary probability vector $[Q^*(f)]_s$; this is the bias interpretation underlying Theorem 7.
--
--   **Formalization Note** The limit is along the natural numbers $N\to\infty$ in the product topology on vectors; the $N=0$ term, where Lean sets $0^{-1}=0$, does not affect the limit. No hypothesis is placed on $f$.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1294, §5, (27)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Overtake_Criteria
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Overtake

/-- **(27).** `y(f) = lim_{N→∞} N⁻¹ Σ_{n=1}^N [V^n(f^∞) − nx(f)]`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1294, §5, (27).

**Formalization Note.** The limit is in `St → ℝ` with the product (coordinatewise) topology,
along `atTop` on `ℕ`; `Σ_{n=1}^N` is `Finset.Icc 1 N`, `nx(f)` is `(n : ℝ) • x(f)`. The
`N = 0` term of the sequence is `0⁻¹ • 0 = 0` and does not affect the limit. No hypothesis on
`f`: the paper states (27) for every `f ε F`. -/
theorem display_27 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
        ∑ n ∈ Finset.Icc 1 N, (Vn M (Policy.stationary f) n - (n : ℝ) • M.x f))
      atTop (𝓝 (M.y f)) := by sorry

end VeinottNoDiscount.Overtake
