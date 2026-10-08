-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_theorem8
-- name    : SongZipkinFluct.Monotone.theorem8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:27.633781+00:00
-- url     : https://prove2.me/theorems/0f7b8fd0-2003-4237-a2f8-0409f0c2c9ce
-- title:
--   Theorem 8 — the myopic and optimal basestock levels y⁺(i), y*(i), y*_∞(i) are nondecreasing in the world state
-- statement:
--   Assume the standing hypotheses of the model, Assumption 1 ($\alpha\bar c < p$) and Condition 1 for a partial order $\preceq$ on the world states: the world chain is stochastically partial-monotone, and the demand rate $\lambda_i$ is nondecreasing in $i$. In the linear-cost model ($K = 0$, $W_0 \equiv 0$) let
--
--   1. $y^+(i)$ be the smallest minimizer of the myopic cost $G^+(i,\cdot)$;
--   2. $y^*(i)$ be the smallest minimizer of $G_\infty(i,\cdot) = \lim_n G_n(i,\cdot)$;
--   3. $y^*_\infty(i) = \lim_{n\to\infty} y^*_n(i)$, where $y^*_n(i)$ is the smallest minimizer of $G_n(i,\cdot)$.
--
--   These all exist, and
--   $$i \preceq j \implies y^+(i) \le y^+(j),\quad y^*(i) \le y^*(j),\quad y^*_\infty(i) \le y^*_\infty(j).$$
--
--   The paper shows (Theorem 2) that the world-dependent basestock policy with levels $y^*(i)$ is optimal for the infinite-horizon problem. Theorem 8 adds that when higher world states mean stochastically higher future demand rates, the optimal, the limiting and the myopic basestock levels all increase with the world state.
--
--   **Formalization Note.** The statement first asserts the existence of the smallest minimizers $y^+(i)$, $y^*(i)$, $y^*_n(i)$ ($n \ge 1$) and of the limits $\lim_n y^*_n(i)$, so that the monotonicity claim is not vacuous. It then asserts monotonicity for every choice of these objects.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 360, §4.2, Theorem 8

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Condition1
import Definitions.Def_SongZipkinFluct_Monotone_Recursion

open Filter Topology

namespace SongZipkinFluct.Monotone

/-- **Theorem 8** (Song and Zipkin 1993, §4.2, p. 360): "Under condition 1, `y⁺(i)`, `y*(i)` and
`y*_∞(i)` are all nondecreasing in `i`."

Here `y⁺(i)` is the smallest minimizer of the myopic cost `G⁺(i, ·)` (p. 356), `y*(i)` the smallest
minimizer of `G_∞(i, ·)` (Theorem 2(b), p. 357) and `y*_∞(i) = lim_n y*_n(i)`, where `y*_n(i)` is the
smallest minimizer of `G_n(i, ·)` (Theorem 1(a) (printed "Theorem 4"), p. 357; Corollary 2, p. 357),
all in the linear-cost model (`K = 0`, `W₀ ≡ 0`).

**Formalization Note.** The statement first asserts that these objects exist (the smallest
minimizers, and the limit of `y*_n(i)`), so the monotonicity claim is not vacuous; then it asserts
monotonicity for every choice of them. -/
theorem theorem8 {I : Type} [Countable I] [Nonempty I] [DecidableEq I] [PartialOrder I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) (hC : M.Condition1) :
    (∃ yplus : I → ℤ, ∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) ∧
    (∃ ystar : I → ℤ, ∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) ∧
    (∃ ys : ℕ → I → ℤ, (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) ∧
      ∀ i, ∃ y : ℤ, Tendsto (fun n => ys n i) atTop (𝓝 y)) ∧
    ∀ (yplus ystar yinf : I → ℤ) (ys : ℕ → I → ℤ),
      (∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i)) →
      (∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i)) →
      (∀ n : ℕ, 1 ≤ n → ∀ i, IsSmallestMinimizer (M.Gn 0 0 n i) (ys n i)) →
      (∀ i, Tendsto (fun n => ys n i) atTop (𝓝 (yinf i))) →
      Monotone yplus ∧ Monotone ystar ∧ Monotone yinf := by sorry

end SongZipkinFluct.Monotone
