-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_lemma6
-- name    : SongZipkinFluct.FixedCost.lemma6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:51.723384+00:00
-- url     : https://prove2.me/theorems/a0a3629c-5105-4d48-8009-250d420e32ca
-- title:
--   Lemma 6 — ΔW_n ≤ ΔW₀, ΔG_n ≤ ΔG₀, and ΔG_n ≤ ΔG⁺ below y⁺_min
-- statement:
--   In the fixed-cost model (standing hypotheses, $\alpha\bar c < p$, $K > 0$, $W_0 = W_\infty$ and $G_0 = G_\infty$ of the linear model), for every world state $i$, every integer $x$ and every $n \ge 1$:
--   1. $\Delta W_n(i, x) \le \Delta W_0(i, x)$;
--   2. $\Delta G_n(i, x) \le \Delta G_0(i, x)$;
--   3. $\Delta G_n(i, x) \le \Delta G^+(i, x)$ whenever $x < y^+_{\min}$,
--
--   where $\Delta f(i, x) = f(i, x+1) - f(i, x)$, $y^+(i)$ is the smallest minimizer of $G^+(i, \cdot)$ and $y^+_{\min} = \min_i y^+(i)$.
--
--   This comparison of differences between the fixed-cost and the linear-cost iterates is what makes the lower bounds of Theorem 4 possible; it depends on the choice of $W_0$ as the linear model's optimal cost.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 358, Lemma 6 (proof pp. 367–368)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Lemma 6 (p. 358; proof pp. 367–368) of Song and Zipkin (1993). Fixed-cost model of §3.2
(`K = K̄F̃_L(α) > 0`, `W₀ = W_∞` and `G₀ = G_∞` of the linear model). For any fixed `x` and
all `n ≥ 1`:

* (a) `ΔW_n(i, x) ≤ ΔW₀(i, x)`;
* (b) `ΔG_n(i, x) ≤ ΔG₀(i, x)`;
* (c) `ΔG_n(i, x) ≤ ΔG⁺(i, x)` for `x < y⁺_min`, where `y⁺(i)` is the smallest minimizer of
  `G⁺(i, ·)` and `y⁺_min = min_i y⁺(i)`.

Formalization Note: `Δf(i, x) = f(i, x + 1) − f(i, x)` (p. 354); `i` is universally
quantified. In (c), `y⁺` and `y⁺_min` are taken through their defining properties. -/
theorem lemma6 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) :
    ∀ n : ℕ, 1 ≤ n → ∀ (i : I) (x : ℤ),
      diff (Wfix M n) i x ≤ diff (Wlin M) i x ∧
      diff (Gfix M n) i x ≤ diff (Glin M) i x ∧
      ∀ (yplus : I → ℤ) (ymin : ℤ), IsYPlus M yplus → IsYPlusMin yplus ymin → x < ymin →
        diff (Gfix M n) i x ≤ diff M.Gplus i x := by sorry

end SongZipkinFluct.FixedCost
