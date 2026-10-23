-- Prove2me | Theorems.Thm_RepRegion_Density_theorem_6_4
-- name    : RepRegion.Density.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:05.008995+00:00
-- url     : https://prove2.me/theorems/7d7a4185-da69-45d2-8eff-fff7c8daa394
-- title:
--   Theorem 6.4, p. 26 — for an arbitrarily precise family, ĝ_n(·; f_m) → g_X uniformly on the coverage region, m → ∞ after n → ∞, a.s.
-- statement:
--   Let $(M, d)$ be a metric space whose closed balls are measurable, let $X_1, X_2, \dots$ be i.i.d. with law $P_X$, and let $\mu$ be a measure on $M$ such that $P_X$ has density $g_X \ge 0$ with respect to $\mu$. Suppose the support $K$ of $P_X$ is compact with $P_X(K) = 1$. Let $\{(\mathcal C, f_m) : m \in \mathbb N\}$ be an arbitrarily precise family of RRS methods, where $(\mathcal C, \Theta, R)$ is a uniform-scale class that is uniformly continuous with respect to $P_X$, and suppose each $(\mathcal C, f_m)$ is uniformly positive with respect to $\mu$. If $g_X$ is uniformly continuous on $M$, then almost surely
--   $$\lim_{m \to \infty} \Bigl( \limsup_{n \to \infty} \sup_{x \in C_n(f_m)} \bigl|g_X(x) - \hat g_n(x; f_m)\bigr| \Bigr) = 0.$$
--
--   The density estimate converges uniformly on the coverage region, provided the methods become fine enough. Outside the coverage region the estimate is $0$, so the convergence cannot be uniform on the whole support; Theorem 6.5 handles that part in integrated form.
--
--   **Formalization Note.** The page assumes $g_X$ *continuous* on $M$; the statement assumes it *uniformly continuous*. With only continuity the statement is false for a general reference measure: take $M = \mathbb R$, $\mu$ Lebesgue measure on $[-1, 1]$ plus unit atoms at $10, 20, 30, \dots$, $g_X$ the tent density on $[-1, 1]$ plus, for each $k$, a continuous bump of height $1$ centred at $10k + 1/(2(k+1))$ with support of width $1/(2(k+1))$, so that $g_X(10k) = 0$ and the bumps lie in a $\mu$-null set; the class of closed balls of radius in $(0, 1]$; and $f_m(S)$ the balls of radius $1/(m+1)$ around the points of $S \cap [-1, 1]$ together with $B[10m; 1/(m+1)]$ (uniformly positive with $\gamma_m = 1/(m+1)$); at a bump point $x$ near $10m$, $g_X(x) = 1$ while $\hat g_n(x; f_m) = 0$. The proof on p. 27 uses exactly uniform continuity ("$|g_X(y) - g_X(x)| \le \varepsilon/2$ for any $y \in A$" from a small diameter of $A$). When $\mu$ charges every non-empty open set (e.g. Lebesgue measure on $\mathbb R^d$), a continuous density of a compactly supported law vanishes off $K$ and is automatically uniformly continuous, so nothing changes in the paper's examples. The regions output by the methods are assumed to have finite $\mu$-measure, so that $\hat g$ is defined. Suprema and the limit superior are taken in $[0, \infty]$.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 26, Theorem 6.4

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem theorem_6_4 {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (μ : Measure M) (g : M → ℝ) (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hdens : P.map (X 0) = μ.withDensity (fun x => ENNReal.ofReal (g x)))
    (K : Set M) (hK : K = supp (P.map (X 0))) (hKc : IsCompact K)
    (hK1 : P.map (X 0) K = 1)
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (f : ℕ → Finset M → Finset (Set M)) (hf : ∀ m, IsRRSMethod C (f m))
    (hAP : ArbitrarilyPrecise P X f)
    (hpos : ∀ m, UniformlyPositive C (f m) μ)
    (hfin : ∀ (m : ℕ) (S : Finset M), ∀ A ∈ f m S, μ A ≠ ⊤)
    (hguc : UniformContinuous g) :
    ∀ᵐ ω ∂P, Tendsto (fun m : ℕ => limsup (fun n : ℕ =>
        ⨆ x ∈ coverage (f m) (sample X n ω),
          ENNReal.ofReal |g x - ghat μ (f m) X n ω x|) atTop) atTop (𝓝 0) := by sorry

end RepRegion.Density
