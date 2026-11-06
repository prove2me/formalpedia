-- Prove2me | Theorems.Thm_PrefixVR_theorem_1
-- name    : PrefixVR.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:34.515137+00:00
-- url     : https://prove2.me/theorems/693bcf59-fa5f-4166-9dd7-c976fa66aed9
-- title:
--   Theorem 1 — $\mathbb E\|\nabla f(x_\tau)\|^2\le 4L\sqrt{2n}\,\Delta_f/T$ with at most $n+5T$ queries and $O(d)$ memory
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n:\mathbb R^d\to\mathbb R$ satisfy **Assumption 1** (each $f_i$ continuously differentiable with $\|\nabla f_i(x)-\nabla f_i(y)\|\le L\|x-y\|$, $L>0$) and let $f=\frac1n\sum_i f_i$ satisfy **Assumption 2** ($f_*=\inf_x f(x)>-\infty$; $\Delta_f=f(x_1)-f_*$). Run Algorithm 1 from $x_1$ with
--   $$
--   \eta=\frac1{2L\sqrt{2n}} .
--   $$
--   Then for every $T\ge1$:
--
--   1. $$\mathbb E\,\|\nabla f(x_\tau)\|^2\le\frac{4L\sqrt{2n}\,\Delta_f}{T},\qquad(10)$$ where $\tau$ is uniform on $[T]$ and the expectation is over $\tau$ and all estimator samples;
--   2. on every outcome, the method makes at most $n+5T$ component-gradient queries;
--   3. the method uses $O(d)$ working memory.
--
--   The method never recomputes a full gradient after initialization and stores no table of component gradients. Taking $T=\max\{1,\lceil4L\sqrt{2n}\Delta_f/\epsilon^2\rceil\}$ gives $\mathbb E\|\nabla f(x_\tau)\|^2\le\epsilon^2$ with $O(n+\sqrt nL\Delta_f/\epsilon^2)$ component-gradient queries (Remark 1).
--
--   **Formalization Note** Assumption 1 is $0<L$ and the published `IsBetaSmooth (fi i) (g i) L` for each $i$; Assumption 2 is `BddBelow (Set.range f)` with $f_*$ = `⨅ x, f x`; $\nabla f$ is Mathlib's `gradient`. The run reaches the gradients only through a logging oracle, and the query count is the length of the log. Clause 3 is read structurally: the algorithm is the iteration of `step` on `State d`, a record of four vectors of $\mathbb R^d$ (current point, active estimate, prefix accumulator, saved output); it is not a separate Lean conjunct.
--
--   Differences from the source:
--   - encoding: Assumption 1: fᵢ continuously differentiable and L-smooth, L > 0 → 0 < L and IsBetaSmooth (fi i) (g i) L for every i, with g i the gradient map; reason: a Lipschitz gradient is continuous, so the same functions qualify
--   - encoding: Assumption 2: f_* := inf f > −∞, Δ_f = f(x₁) − f_* → BddBelow (Set.range f), Δ_f = f x₁ − ⨅ x, f x; reason: a real infimum of a set bounded below is the true infimum
--   - encoding: the expectation over the estimator samples of the run of Algorithm 1 → the uniform average over the finite sample space Sample n T (output index τ and the draws (j_t, i_t) of updates t ≤ T, with one-point or unused dummy draws where the paper draws nothing), for a horizon T containing every time in the statement; reason: independent uniform draws on finite sets have the uniform product law; unused coordinates and later draws change no expectation of quantities up to the stated times
--   - encoding: "makes at most n + 5T component-gradient queries" → the length of the run's query log is ≤ n + 5T on every outcome; reason: the algorithm reaches ∇fᵢ only through the logging oracle; each evaluation is one entry
--   - reading: "uses O(d) working memory" (no machine model given) → structural: Algorithm 1 is the iteration of step on State d, four vectors of ℝᵈ, with counters and draws passed as arguments, after an init that accumulates v₁ in one running vector; no separate conjunct; reason: §3.4 and App. C describe the memory as a constant number of d-dimensional vectors plus counters; there is no bit-complexity model to state it in
--   - encoding: components i ∈ [n] = {1, …, n} → Fin n, paper index i is i − 1, with NeZero n; reason: Lean convention; n ≥ 1 is the paper's standing setting of a finite sum
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), §3.3, Theorem 1, Eq. (10), p.6 (PDF p.6); proof App. C, p.16

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample
import Definitions.Def_PrefixVR_run

namespace PrefixVR

/-- **Theorem 1.** Jiang, Wang, Yang, Li, Zhang, *Memory-efficient Finite-sum Optimization without
Full Gradient Refreshes* (manuscript, sha256 ed33106a…), Theorem 1, Eq. (10), p.6: "Under
Assumptions 1 and 2, run Algorithm 1 with η = 1/(2L√2n). Then, for every T ≥ 1,
𝔼‖∇f(x_τ)‖² ≤ 4L√2nΔ_f/T. The method makes at most n + 5T component-gradient queries and uses
O(d) working memory."

For every `n ≥ 1`, `d`, `L > 0`, components `fᵢ` satisfying Assumption 1 with gradient maps
`g i = ∇fᵢ`, `f = (1/n) ∑ fᵢ` bounded below, every `x₁` and `T ≥ 1`, Algorithm 1 with
`η = 1/(2L√(2n))`:
1. `𝔼‖∇f(x_τ)‖² ≤ 4L√(2n)(f(x₁) − f_*)/T`, the expectation over `τ` and all estimator samples;
2. on every outcome, the query log has length at most `n + 5T`.

**Formalization Note.** Assumption 1 is `0 < L` and `IsBetaSmooth (fi i) (g i) L` for every `i`
(published `ConvexOptAlg.SmoothGD.IsBetaSmooth`); Assumption 2 is `BddBelow (Set.range f)` with
`f_* = ⨅ x, f x`; `f = KatyushaNs.favg fi`; `∇f` is Mathlib's `gradient`. The run (`run`, built
from `init` and `step`) reaches the gradients only through the logging oracle, so the length of
`queryLog` is the number of component-gradient queries. The O(d) working-memory clause is read
structurally: the algorithm is the iteration of `step` on `State d`, a record of four vectors of
`ℝᵈ` (current point, active estimate, prefix accumulator, saved output); no stored object grows
with `n` or `T`. -/
theorem theorem_1 {n d : ℕ} [NeZero n] (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 0 < L)
    (hA1 : ∀ i, ConvexOptAlg.SmoothGD.IsBetaSmooth (fi i) (g i) L)
    (hA2 : BddBelow (Set.range (KatyushaNs.favg fi)))
    (x₁ : EuclideanSpace ℝ (Fin d)) (T : ℕ) (hT : 1 ≤ T) :
    expect (fun ω : Sample n T =>
        ‖gradient (KatyushaNs.favg fi)
          (output g (1 / (2 * L * Real.sqrt (2 * n))) x₁ ω)‖ ^ 2)
      ≤ 4 * L * Real.sqrt (2 * n) * (KatyushaNs.favg fi x₁ - ⨅ x, KatyushaNs.favg fi x) / T ∧
    ∀ ω : Sample n T,
      (queryLog g (1 / (2 * L * Real.sqrt (2 * n))) x₁ ω).length ≤ n + 5 * T := by sorry

end PrefixVR
