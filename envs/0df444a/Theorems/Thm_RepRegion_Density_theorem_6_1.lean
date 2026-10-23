-- Prove2me | Theorems.Thm_RepRegion_Density_theorem_6_1
-- name    : RepRegion.Density.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:02.702683+00:00
-- url     : https://prove2.me/theorems/7b7976da-80cb-42e3-b7d4-41d457799697
-- title:
--   Theorem 6.1, p. 22 — a uniform-scale class, uniformly continuous w.r.t. P_X with compact support, is Glivenko–Cantelli
-- statement:
--   Let $(M, d)$ be a metric space whose closed balls are measurable, and let $X_1, X_2, \dots$ be i.i.d. $M$-valued random variables with law $P_X$ and empirical measures $\hat P_{X,n}$. Let $(\mathcal C, \Theta, R)$ be a uniform-scale class of regions in $M$ that is uniformly continuous with respect to $P_X$, and suppose that the support $K$ of $P_X$ is compact with $P_X(K) = 1$. Then
--   $$\sup_{R(\theta, \lambda) \in \mathcal C} \bigl|\hat P_{X,n}(R(\theta, \lambda)) - P_X(R(\theta, \lambda))\bigr| \xrightarrow[n \to \infty]{\text{a.s.}} 0.$$
--
--   That is, $\mathcal C$ is a Glivenko–Cantelli class for $P_X$. The hypotheses are geometric (regions swell uniformly with the scale) and measure-theoretic (probabilities change uniformly with the scale) rather than combinatorial: no finite VC dimension is assumed. The result drives every later convergence statement of the mission.
--
--   **Formalization Note.** The supremum is taken in $[0, \infty]$. The clause $P_X(R(\theta, \lambda)) \le P_X(R(\theta, \lambda - \delta)) + \varepsilon$ of uniform continuity is read with $R(\theta, \lambda - \delta) = \emptyset$ when $\lambda \le \delta$, so it requires regions of small scale to have small probability. Dropping that clause at small scales makes the statement false: on $M = [0, 1]$ with the uniform law, the regions $\{x : \operatorname{dist}(x, T) \ge |T|^{-2} - \lambda\}$ indexed by finite sets $T$ satisfy every other hypothesis, yet the region with $T = S_n$ and $\lambda = 1/(2n^2)$ contains no observation and has probability at least $1 - 1/n$.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 22, Theorem 6.1

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem theorem_6_1 {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (K : Set M) (hK : K = supp (P.map (X 0))) (hKc : IsCompact K)
    (hK1 : P.map (X 0) K = 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      ⨆ A ∈ C, ENNReal.ofReal |empFreq X n ω A - (P.map (X 0) A).toReal|) atTop (𝓝 0) := by sorry

end RepRegion.Density
