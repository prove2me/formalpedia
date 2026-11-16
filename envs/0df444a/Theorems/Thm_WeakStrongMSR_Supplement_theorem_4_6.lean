-- Prove2me | Theorems.Thm_WeakStrongMSR_Supplement_theorem_4_6
-- name    : WeakStrongMSR.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:35:08.052699+00:00
-- url     : https://prove2.me/theorems/0d56b1a7-0c24-439b-b6a8-d0249ad9f778
-- title:
--   Theorem 4.6 — $\Omega(k\log n)$ expected strong queries for constant success probability, $n=k^2$
-- statement:
--   Fix an approximation factor $\alpha\ge1$, a corruption probability $\delta\in(0,\tfrac12)$ and a success probability $\rho\in(0,1]$. There are a constant $c>0$ and a $k_0$ such that for every $k\ge k_0$, with $n=k^2$ points, the following holds. Let $\Delta\ge\alpha k^2$ be a known upper bound on the aspect ratio (§2.3), and let $A$ be any (admissible) randomized adaptive strong-query algorithm for $n=k^2$ points and $k$ balls, which may depend on $\Delta$, that, on **every** instance — every metric $d$ on the points with aspect ratio at most $\Delta$, and every adversary — returns an $\alpha$-approximate minimum-sum-of-radii solution with probability at least $\rho$. Then on **some** such instance,
--   $$\mathbb E[Q]\ \ge\ c\,k\ln n=c\,k\ln(k^2).$$
--
--   So the $\Omega(k\log n)$ lower bound holds even for algorithms that are only required to succeed with a constant probability, in the regime $n=k^2$.
--
--   **Formalization Note** The algorithm model is `WeakStrongMSR.Supplement.QueryAlg`, as in Theorem 4.5. The constants $c$ and $k_0$ depend only on $\alpha,\delta,\rho$ (not on $\Delta$).
--
--   Differences from the source:
--   - generalization: the algorithm knows an aspect-ratio bound $\Delta\le n^{O(1)}$ (§2.3, p.5); Theorem 4.6 does not name $\Delta$ → for every $\Delta\ge\alpha k^2$, success is required only on metrics of aspect ratio at most $\Delta$, the algorithm may depend on $\Delta$, and the hard instance has aspect ratio at most $\Delta$; reason: the lower bound must cover the algorithms of the paper's own model, which know $\Delta$; the hard metric has aspect ratio $2\alpha(K+1)\le\alpha(k+1)\le\alpha k^2$, so the proof is unchanged; the statement without $\Delta$ is the special case $\Delta=\alpha k^2$
--   - reading: "every algorithm", "on every instance", constants of $\Omega(\cdot)$ depending on $\alpha,\delta,\rho$ (p.29) → every admissible `QueryAlg` (measurable in its coins); success for every metric $d$ with positive distances (and aspect ratio at most $\Delta$) and every adversary; strong queries are the point queries of Definition 1.1; $\exists c>0$ after $\alpha,\delta,\rho$ and before $k,\Delta$ and the algorithm; reason: §4, p.29 fixes $\alpha\ge1$, $\delta\in(0,\tfrac12)$ and lets the constants depend on them and on the success probability; an instance is a metric and an adversary of the model; every algorithm that can be run is measurable in its coins
--   - encoding: randomized algorithm, "in expectation", $\log n$ with $n=k^2$ → coin tape with law `tapeLaw`; $\mathbb E[Q]$ in $[0,\infty]$; $\ln(k^2)$; reason: uniform coins simulate any randomness; the base of the logarithm only changes $c$
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Theorem 4.6, p.33 (PDF 34); proof p.33; model §4, p.29 (PDF 30)

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

/-- **Theorem 4.6** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong
and Weak Oracles*, manuscript, sha256 5f8fbaf3…67e8f92a0, p.33, PDF p.34). "Fix ρ ∈ (0, 1]. For all
sufficiently large k, let n = k². Every algorithm that returns an α-approximate
minimum-sum-of-radii solution with probability at least ρ on every instance makes Ω(k log n)
strong queries in expectation on some instance."

For every approximation factor `α ≥ 1`, corruption probability `δ ∈ (0, 1/2)` and `ρ ∈ (0, 1]`
there are `c > 0` and `k₀` such that for every `k ≥ k₀`, with `n = k²`, and every known
aspect-ratio bound `Δ ≥ α·k²`, every admissible randomized adaptive strong-query algorithm `A` for
`(k², k)` that succeeds with probability at least `ρ` on every instance (every metric `d` on
`Fin (k²)` of aspect ratio at most `Δ` and every adversary) makes at least `c · k · log (k²)`
strong queries in expectation on some such instance.

**Formalization Note.** §4, p.29: the constants in Ω(·) may depend on `α`, `δ` and the required
success probability `ρ`, so `c` is chosen after `α, δ, ρ` and before `k, A`. The algorithm model is
`QueryAlg` (as in Theorem 4.5). As in Theorem 4.5, the algorithm may know an aspect-ratio bound
`Δ ≥ α·n = α·k²` (§2.3, p.5), need only succeed on metrics of aspect ratio at most `Δ`, and the hard
instance has aspect ratio at most `Δ` (the hard metric's is `2α(K + 1) ≤ α(k + 1) ≤ α·k²`). The
logarithm is natural. -/
theorem theorem_4_6 :
    ∀ α : ℝ, 1 ≤ α → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ Δ : ℝ, α * ((k : ℝ) ^ 2) ≤ Δ →
      ∀ A : QueryAlg (k ^ 2) k, A.Admissible →
        (∀ d : Fin (k ^ 2) → Fin (k ^ 2) → ℝ, MinSumClust.IsMetric d → aspectRatio d ≤ Δ →
          ∀ adv : Adversary (k ^ 2), ENNReal.ofReal ρ ≤ A.succProb α δ d adv) →
        ∃ d : Fin (k ^ 2) → Fin (k ^ 2) → ℝ, MinSumClust.IsMetric d ∧ aspectRatio d ≤ Δ ∧
          ∃ adv : Adversary (k ^ 2),
          ENNReal.ofReal (c * k * Real.log ((k : ℝ) ^ 2)) ≤ A.expQueries δ d adv := by sorry

end WeakStrongMSR.Supplement
