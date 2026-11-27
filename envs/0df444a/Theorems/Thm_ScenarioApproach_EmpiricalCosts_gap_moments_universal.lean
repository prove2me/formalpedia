-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_gap_moments_universal
-- name    : ScenarioApproach.EmpiricalCosts.gap_moments_universal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T06:49:54.441767+00:00
-- url     : https://prove2.me/theorems/51427ff2-f246-50ca-898f-96ac17bb144e
-- title:
--   The mixed moments of the gaps between the risks $R_d,\dots,R_N$ are distribution-free
-- statement:
--   Consider the scenario program (1.4) with decision $\nu\in\mathbb R^{d-1}$, $d=n+1$, and $N\ge d$ scenarios $\delta_1,\dots,\delta_N$ drawn independently from a probability $\mathbb P$ on $\Delta$. Let $\nu^*$ be its solution, $\ell^*_1\ge\cdots\ge\ell^*_N$ the empirical costs (Definition 8.1) and $R_k=\mathbb P\{\delta:\ell(\nu^*,\delta)>\ell^*_k\}$ their risks (Definition 8.2), so that $0\le R_d\le R_{d+1}\le\cdots\le R_N\le1$. Define the gap vector $G=(G_0,\dots,G_{N-d})$ by
--
--   $$
--   G_i=R_{d+i+1}-R_{d+i}\quad(d+i<N),\qquad G_{N-d}=1-R_N .
--   $$
--
--   Let $(\Delta,\mathbb P,\ell)$ and $(\Delta',\mathbb P',\ell')$ be two problems with the same $n$ and $N$, each satisfying the standing assumptions of the book: $\ell(\cdot,\delta)$ convex for every $\delta$, $(\nu,\delta)\mapsto\ell(\nu,\delta)$ measurable, existence and uniqueness of the solution for every sample size $m\ge1$ and every sample, nondegeneracy (Definition 8.3), and a measurable solution map $\nu^*$. Then for every $M\ge0$ and every word $a:\{1,\dots,M\}\to\{0,\dots,N-d\}$,
--
--   $$
--   \mathbb E_{\mathbb P^N}\Big[\prod_{j=1}^{M}G_{a(j)}\Big]=\mathbb E_{\mathbb P'^N}\Big[\prod_{j=1}^{M}G'_{a(j)}\Big].
--   $$
--
--   In other words, the mixed moments of the gaps between consecutive risks do not depend on $\Delta$, $\mathbb P$ or $\ell$. Together with moment determinacy on the cube this shows that the joint law of $(R_d,\dots,R_N)$ is the same for all nondegenerate problems, which is the distribution-free content of Theorem 8.4.
--
--   **Formalization Note** The risks are `empiricalRisk P ℓ ω (νstar ω) k`; the gap $G_{a(j)}$ is written out inline with the convention $R_{N+1}=1$.
-- source:
--   Intermediate step in the proof of M. C. Campi, S. Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, doi:10.1137/1.9781611975444, Chapter 8, Sec. 8.1, p. 90, Theorem 8.4 (stated without proof); A. Carè, S. Garatti, M. C. Campi, Scenario min-max optimization and the risk of empirical costs, SIAM J. Optim. 25(4):2061-2080, 2015, doi:10.1137/130928546. The moment $\mathbb E\prod_j G_{a(j)}$ equals the probability that $M$ further independent scenarios fall into prescribed gaps of the empirical costs, which by exchangeability of the $N+M$ scenarios is a combinatorial constant.

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_risk
import Definitions.Def_ScenarioApproach_EmpiricalCosts_nondegenerate
namespace ScenarioApproach.EmpiricalCosts

/-- The mixed moments of the gaps between the risks `R_d ≤ R_{d+1} ≤ ⋯ ≤ R_N ≤ 1` of the empirical
costs of the scenario program (1.4) (`ν ∈ ℝ^n`, `d = n + 1`, `N ≥ d`) are distribution-free:
for two problems `(Δ, ℙ, ℓ)` and `(Δ', ℙ', ℓ')` satisfying the standing assumptions
(convexity, measurability, existence and uniqueness, nondegeneracy), and every word
`a : Fin M → {0, …, N - d}`, `𝔼 ∏ⱼ G_{a(j)} = 𝔼' ∏ⱼ G'_{a(j)}`, where the gap vector is
`G_i = R_{d+i+1} - R_{d+i}` for `d + i < N` and `G_{N-d} = 1 - R_N`. -/
theorem gap_moments_universal {n N : ℕ} {Δ Δ' : Type*} [MeasurableSpace Δ] [MeasurableSpace Δ']
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    (hmeas : Measurable (Function.uncurry ℓ))
    (hexu : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ, ∃! ν, IsSolution ℓ ω ν)
    (hnd : Nondegenerate P ℓ)
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (P' : MeasureTheory.Measure Δ') [MeasureTheory.IsProbabilityMeasure P']
    (ℓ' : EuclideanSpace ℝ (Fin n) → Δ' → ℝ)
    (hconv' : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ' ν δ)
    (hmeas' : Measurable (Function.uncurry ℓ'))
    (hexu' : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ', ∃! ν, IsSolution ℓ' ω ν)
    (hnd' : Nondegenerate P' ℓ')
    (νstar' : (Fin N → Δ') → EuclideanSpace ℝ (Fin n))
    (hνstar' : ∀ ω, IsSolution ℓ' ω (νstar' ω)) (hνstar_meas' : Measurable νstar')
    (hN : n + 1 ≤ N) {M : ℕ} (a : Fin M → Fin (N - (n + 1) + 1)) :
    ∫ ω, ∏ j, ((if n + 1 + (a j : ℕ) < N then empiricalRisk P ℓ ω (νstar ω) (n + 1 + a j + 1)
          else 1) - empiricalRisk P ℓ ω (νstar ω) (n + 1 + a j))
        ∂(MeasureTheory.Measure.pi fun _ : Fin N => P) =
      ∫ ω, ∏ j, ((if n + 1 + (a j : ℕ) < N then empiricalRisk P' ℓ' ω (νstar' ω) (n + 1 + a j + 1)
          else 1) - empiricalRisk P' ℓ' ω (νstar' ω) (n + 1 + a j))
        ∂(MeasureTheory.Measure.pi fun _ : Fin N => P') := by sorry

end ScenarioApproach.EmpiricalCosts
