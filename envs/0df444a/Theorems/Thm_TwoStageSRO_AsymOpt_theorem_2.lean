-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_theorem_2
-- name    : TwoStageSRO.AsymOpt.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:51.717987+00:00
-- url     : https://prove2.me/theorems/ba308b37-3e82-4724-9cfb-a551437dae8e
-- title:
--   Theorem 2, p. 12 — under [A1]–[A4], v̂^SRO_N and v̂^MP_N converge a.s. to v*, and accumulation points of their optimal first-stage decisions are a.s. optimal
-- statement:
--   Let $\xi^1,\xi^2,\dots$ be independent random vectors in $\mathbb R^d$ with common law $\mu$, supported in the polyhedron $\Xi$ ($P(\xi\in\Xi)=1$), and consider the two-stage stochastic linear problem (OPT) with optimal value $v^*$, its sample robust optimization problem (SRO) with uncertainty sets $U^i_N=\{\zeta\in\Xi:\|\zeta-\xi^i\|\le\epsilon_N\}$, and its multi-policy approximation (MP). Assume
--
--   1. [A1] $\Pi=\mathcal L$ (linear decision rules) and $\epsilon_N\to0$ as $N\to\infty$;
--   2. [A2] $v^*$ is finite and $\mathbb E\|\xi\|<\infty$;
--   3. [A3] the set of optimal first-stage decisions of (OPT) is nonempty and bounded;
--   4. [A4] there exist $x\in\mathbb R^n$ and $\epsilon>0$ such that for every $\hat\zeta\in\Xi$ some $y^{\hat\zeta}(\cdot)\in\mathcal L$ satisfies $Tx+Wy^{\hat\zeta}(\zeta)\ge h(\zeta)$ for all $\zeta\in B(\hat\zeta,\epsilon)\cap\Xi$.
--
--   Then
--   $$\lim_{N\to\infty}\hat v^{SRO}_N=\lim_{N\to\infty}\hat v^{MP}_N=v^*\quad\text{almost surely.}$$
--   Moreover, if $\hat x^{SRO}_N$ and $\hat x^{MP}_N$ are optimal first-stage decisions of (SRO) and (MP), then almost surely every accumulation point of $(\hat x^{SRO}_N)$ or of $(\hat x^{MP}_N)$ is an optimal first-stage decision of (OPT).
--
--   This is the paper's main result: the multi-policy approximation with linear decision rules, a linear or second-order cone program of size $O(N)$, is asymptotically optimal for two-stage stochastic linear optimization, including problems without relatively complete recourse.
--
--   **Formalization Note** The samples are `ξ 0, ξ 1, …` on a probability space, independent (`iIndepFun`) with law $\mu$ (`HasLaw`), and $\mu(\Xi^c)=0$. The radii form a deterministic sequence $\epsilon_N\ge0$, and the $\ell_p$-norm is arbitrary, $p\in[1,\infty]$. Values are `EReal` infima; "finite" means $\ne\pm\infty$; $\mathbb E\|\xi\|<\infty$ is `Integrable id μ`. Since optimal decisions need not exist for every $N$, the accumulation-point clauses quantify, inside one almost-sure event, over every sequence that minimizes $\hat V^{SRO}_N$ (resp. $\hat V^{MP}_N$) for all sufficiently large $N$; accumulation points are `MapClusterPt`.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 12, Theorem 2

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 12, Theorem 2.
Under [A1] (`Π = L`, `ε_N → 0`), [A2] (`v*` finite, `E‖ξ‖ < ∞`), [A3] (the optimal set of (OPT) is
nonempty and bounded) and [A4], almost surely `v̂^SRO_N → v*` and `v̂^MP_N → v*`, and every accumulation
point of optimal first-stage decisions of (SRO) or of (MP) is optimal for (OPT).

**Formalization Note**
* `ξ 0, ξ 1, …` are i.i.d. with law `μ` on a probability space `(Ω, P)`, and `μ(Ξᶜ) = 0` (the paper's
  `P(ξ ∈ Ξ) = 1`, p. 6); the paper's `ξ¹, …, ξᴺ` are `ξ 0 ω, …, ξ (N-1) ω`.
* The radii `ε_N ≥ 0` form a deterministic sequence; the norm is the `ℓp`-norm for an arbitrary
  `p ∈ [1, ∞]`.
* All values are `EReal` infima; "`v*` finite" is `v* ≠ ⊤ ∧ v* ≠ ⊥`; `E‖ξ‖ < ∞` is `Integrable id μ`.
* "Let `x̂_N` be optimal first-stage decisions": the accumulation-point clauses hold, on one almost-sure
  event, for every sequence `x̂_N` that minimizes `V̂^SRO_N` (resp. `V̂^MP_N`) for all large `N`
  (`MapClusterPt` is "accumulation point"). -/
theorem theorem_2 {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P) (hsupp : μ (Xi M)ᶜ = 0)
    (ε : ℕ → ℝ) (hε0 : ∀ N, 0 ≤ ε N) (hε : Tendsto ε atTop (𝓝 0))
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (hA4 : A4 M p) :
    (∀ᵐ ω ∂P,
      Tendsto (fun N => vSRO M p (ε N) (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) ∧
      Tendsto (fun N => vMP M LDR p (ε N) (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ))) ∧
    (∀ᵐ ω ∂P, ∀ xh : ℕ → (Fin n → ℝ),
      (∀ᶠ N in atTop, IsMinOn (VSRO M p (ε N) (fun i => ξ i ω) N) Set.univ (xh N)) →
      ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ) ∧
    (∀ᵐ ω ∂P, ∀ xh : ℕ → (Fin n → ℝ),
      (∀ᶠ N in atTop, IsMinOn (VMP M LDR p (ε N) (fun i => ξ i ω) N) Set.univ (xh N)) →
      ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ) := by sorry

end TwoStageSRO.AsymOpt
