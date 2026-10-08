-- Prove2me | Theorems.Thm_VeinottNoDiscount_Overtake_display_28
-- name    : VeinottNoDiscount.Overtake.display_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:43.296424+00:00
-- url     : https://prove2.me/theorems/50873c4b-1f68-4b97-b156-ff004cbf8282
-- title:
--   (28) — N⁻¹ Σ_{n=1}^N Vⁿ(f^∞) = [(N + 1)/2]x(f) + y(f) + σ(N, f), σ(N, f) → 0
-- statement:
--   Let $f\in F$ be a decision rule with gain $x(f)$ and bias $y(f)$, and let $V^n(f^\infty)$ be the vector of total expected returns in the first $n$ periods under the stationary policy $f^\infty$. Then
--   $$\frac1N\sum_{n=1}^{N}V^n(f^\infty)=\frac{N+1}{2}\,x(f)+y(f)+\sigma(N,f),\qquad \lim_{N\to\infty}\sigma(N,f)=0 .$$
--
--   This is the representation from which Theorem 7 follows: the average of the first $N$ finite-horizon returns grows linearly in $N$ with slope $x(f)/2$, and its constant term is the bias $y(f)$.
--
--   **Formalization Note** $\sigma(N,f)$ is defined as the remainder $N^{-1}\sum_{n=1}^N V^n(f^\infty)-\tfrac{N+1}{2}x(f)-y(f)$, so the statement is that this remainder tends to $0$ coordinatewise as $N\to\infty$ along the natural numbers. The $N=0$ value, where Lean sets $0^{-1}=0$, does not affect the limit.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1294, §5, (28)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Overtake_Criteria
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Overtake

/-- **(28).** `N⁻¹ Σ_{n=1}^N V^n(f^∞) = [(N + 1)/2]x(f) + y(f) + σ(N, f)` where
`lim_{N→∞} σ(N, f) = 0`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1294, §5, (28).

**Formalization Note.** `σ(N, f)` is the remainder `N⁻¹ Σ_{n=1}^N V^n(f^∞) − [(N + 1)/2]x(f)
− y(f)`, so (28) is the assertion that this remainder tends to `0` (coordinatewise, along
`atTop` on `ℕ`). The `N = 0` value (where `0⁻¹ = 0` in Lean) does not affect the limit. -/
theorem display_28 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • (∑ n ∈ Finset.Icc 1 N, Vn M (Policy.stationary f) n)
        - (((N : ℝ) + 1) / 2) • M.x f - M.y f)
      atTop (𝓝 0) := by sorry

end VeinottNoDiscount.Overtake
