-- Prove2me | Theorems.Thm_WeakStrongMSR_Supplement_theorem_4_5
-- name    : WeakStrongMSR.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:34:21.633194+00:00
-- url     : https://prove2.me/theorems/59dd96ed-3e23-4f76-ba61-6f39028ad83d
-- title:
--   Theorem 4.5 — $\Omega(k\log n)$ expected strong queries for high-probability $\alpha$-approximate MSR, $3\le k\le n/\log^2 n$
-- statement:
--   Fix an approximation factor $\alpha\ge1$, a corruption probability $\delta\in(0,\tfrac12)$ and $\beta>0$. There are a constant $c>0$ and an $n_0$ such that the following holds for every $n\ge n_0$ and every integer $k$ with
--   $$3\le k\le \frac{n}{\ln^2 n}.$$
--   Let $\Delta\ge\alpha n$ be a known upper bound on the aspect ratio (the model of §2.3), and let $A$ be any (admissible) randomized adaptive strong-query algorithm for $n$ points and $k$ balls, which may depend on $\Delta$. Suppose that on **every** instance — every metric $d$ on the $n$ points (distinct points at positive distance) with aspect ratio at most $\Delta$, and every adversary — $A$ returns an $\alpha$-approximate minimum-sum-of-radii solution with probability at least $1-n^{-\beta}$, over the corruptions and its coins. Then on **some** such instance $(d,\mathrm{adv})$ (aspect ratio at most $\Delta$),
--   $$\mathbb E[Q]\ \ge\ c\,k\ln n,$$
--   where $Q$ is the number of strong point queries $A$ makes.
--
--   This shows that the $\log n$ factor of the upper bound (Theorem 1.2) cannot be avoided by algorithms that succeed with high probability, even ones that see every weak distance, adapt their queries and output centres they never queried.
--
--   **Formalization Note** The algorithm is the general model `WeakStrongMSR.Supplement.QueryAlg`, not a program of the base mission's machine. The constants $c$ and $n_0$ depend only on $\alpha,\delta,\beta$ (not on $\Delta$).
--
--   Differences from the source:
--   - generalization: the algorithm knows an aspect-ratio bound $\Delta\le n^{O(1)}$ (§2.3, p.5); Theorem 4.5 does not name $\Delta$ → for every $\Delta\ge\alpha n$, success is required only on metrics of aspect ratio at most $\Delta$, the algorithm may depend on $\Delta$, and the hard instance has aspect ratio at most $\Delta$; reason: the lower bound must cover the algorithms of the paper's own model, which know $\Delta$; the hard metric has aspect ratio $2\alpha(K+1)\le\alpha(k+1)\le\alpha n$ (p.29), so the proof is unchanged; an algorithm that succeeds on every metric satisfies the hypothesis for $\Delta=\alpha n$, so the statement without $\Delta$ is the special case $\Delta=\alpha n$
--   - reading: $k\le n/\log^2 n$ with no base printed → $k\le n/(\ln n)^2$, natural logarithm; reason: the paper prints no base; the natural log matches the base mission and gives the larger range of $k$, and the proof needs only $s=\Theta(\log n)$ and $Ks\le n-2$, which hold for any base
--   - reading: "every algorithm", "on every instance", constants of $\Omega(\cdot)$ depending on $\alpha,\delta,\beta$ (p.29) → every admissible `QueryAlg` (measurable in its coins); success for every metric $d$ with positive distances (and aspect ratio at most $\Delta$) and every adversary; strong queries are the point queries of Definition 1.1; $\exists c>0$ after $\alpha,\delta,\beta$ and before $n,k,\Delta$ and the algorithm; reason: §4, p.29 fixes $\alpha\ge1$, $\delta\in(0,\tfrac12)$ and lets the constants depend on them and on the success probability; an instance is a metric and an adversary of the model (Definition 1.1, §2.2); every algorithm that can be run is measurable in its coins
--   - encoding: randomized algorithm, "in expectation" → coin tape with law `tapeLaw`; $\mathbb E[Q]$ in $[0,\infty]$ with $Q=\infty$ on a run that never stops; reason: uniform coins simulate any randomness; an extended-valued expectation is the usual one for nonnegative counts
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Theorem 4.5, p.32 (PDF 33); proof pp.32–33; model §4, p.29 (PDF 30); informal Theorem 1.3, p.2

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Supplement_QueryAlg

open scoped Classical ENNReal

set_option autoImplicit false

namespace WeakStrongMSR.Supplement

open WeakStrongMSR

/-- **Theorem 4.5** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong
and Weak Oracles*, manuscript, sha256 5f8fbaf3…67e8f92a0, p.32, PDF p.33; informal version
Theorem 1.3, p.2). "Fix β > 0. For all sufficiently large n and 3 ≤ k ≤ n/log² n, every algorithm
that returns an α-approximate minimum-sum-of-radii solution with probability at least 1 − n^{−β}
on every instance makes Ω(k log n) strong queries in expectation on some instance."

For every approximation factor `α ≥ 1`, corruption probability `δ ∈ (0, 1/2)` and `β > 0` there
are `c > 0` and `n₀` such that for every `n ≥ n₀`, `3 ≤ k ≤ n/(log n)²` and known aspect-ratio
bound `Δ ≥ α·n`, every admissible randomized adaptive strong-query algorithm `A` for `(n, k)` that
succeeds with probability at least `1 − n^{−β}` on every instance (every metric `d` on `Fin n` of
aspect ratio at most `Δ` and every adversary) makes at least `c · k · log n` strong queries in
expectation on some such instance.

**Formalization Note.** §4, p.29: "δ ∈ (0, 1/2) and the approximation factor α ≥ 1 are fixed
constants. The constants in Ω(·) may depend on α, δ and the required success probability", so
`c` is chosen after `α, δ, β` and before `n, k, A`. The algorithm is the general model
`QueryAlg` (it sees the whole weak table, adapts, is randomized, has unbounded computation, may
output unqueried centres, outputs no assignment). §2.3 (p.5): "we assume that the algorithm knows
an upper bound ∆ ≤ n^{O(1)} on the aspect ratio". So the statement holds for every known bound
`Δ ≥ α·n`: the algorithm (chosen after `Δ`) may use it, it need only succeed on metrics of aspect
ratio at most `Δ`, and the hard instance has aspect ratio at most `Δ` (the paper's hard metric has
aspect ratio `D = 2α(K + 1) ≤ α(k + 1) ≤ α·n`, p.29). An algorithm that succeeds on every metric
satisfies the hypothesis for `Δ = α·n`, so the no-`Δ` reading is a special case. The logarithm is natural (the paper prints no
base; any base gives the same theorem up to `c` and a larger range of `k` for the natural log). -/
theorem theorem_4_5 :
    ∀ α : ℝ, 1 ≤ α → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ β : ℝ, 0 < β →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 3 ≤ k →
      (k : ℝ) ≤ n / Real.log n ^ 2 → ∀ Δ : ℝ, α * n ≤ Δ →
      ∀ A : QueryAlg n k, A.Admissible →
        (∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d → aspectRatio d ≤ Δ →
          ∀ adv : Adversary n, ENNReal.ofReal (1 - (n : ℝ) ^ (-β)) ≤ A.succProb α δ d adv) →
        ∃ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d ∧ aspectRatio d ≤ Δ ∧ ∃ adv : Adversary n,
          ENNReal.ofReal (c * k * Real.log n) ≤ A.expQueries δ d adv := by sorry

end WeakStrongMSR.Supplement
