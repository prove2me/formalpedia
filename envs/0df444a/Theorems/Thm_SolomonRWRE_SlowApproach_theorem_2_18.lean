-- Prove2me | Theorems.Thm_SolomonRWRE_SlowApproach_theorem_2_18
-- name    : SolomonRWRE.SlowApproach.theorem_2_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:49.649394+00:00
-- url     : https://prove2.me/theorems/5aec6494-be96-45b0-8065-e84330adff24
-- title:
--   Theorem (2.18) — limits of passage times to ordinary sites
-- statement:
--   Let $T_n$ be the first passage time to site $n$. In the critical regime $\gamma\theta=1$,
--   $$
--   \frac{T_n}{2n\log_\theta n}\xrightarrow{P}1.
--   $$
--   In the supercritical regime $\gamma\theta>1$, if $n_k\to\infty$ and $\{\log_{1/\gamma}n_k\}\to\varepsilon$, the laws of $n_k^{-\rho}T_{n_k}$ converge to the distribution with Laplace transform
--   $$
--   \exp\left[-Lu\sum_{j\in\mathbb Z}\frac{(\gamma\theta)^{j-\eta}}{1+\mu u\theta^{j-\eta}}\right],
--   $$
--   where $\mu=\nu(1-\gamma)^\rho$, $L=(1-\gamma)\mu/\gamma$, and $\eta=\varepsilon+\log_{1/\gamma}(1-\gamma)$. The Lean statement realizes this law as $(1-\gamma)^\rho$ times a variable with law $F_\eta$ and tests convergence at continuity points.
--
--   This theorem transfers the mirror-indexed limits to deterministic target sites.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 17, Theorem (2.18)

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology

namespace SolomonRWRE.SlowApproach

/-- Solomon, Theorem (2.18), p. 17, both clauses. The second limit distribution is
the law (2.12) scaled by `(1 - γ)^ρ`, with shifted phase. -/
theorem theorem_2_18 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ)
    (γ θ : ℝ) (h : IsMirrorEnvironment P α X γ θ) :
    (γ * θ = 1 →
      MeasureTheory.TendstoInMeasure P
        (fun n ω => ((passage X n ω).toNat : ℝ) /
          (2 * (n : ℝ) * Real.logb θ n)) Filter.atTop (fun _ => 1)) ∧
    (1 < γ * θ → ∀ (F : ℝ → MeasureTheory.Measure ℝ),
      IsLimitLaw F γ θ → ∀ (ns : ℕ → ℕ) (ε : ℝ),
      Filter.Tendsto ns Filter.atTop Filter.atTop →
      Filter.Tendsto (fun k => Int.fract (Real.logb (1 / γ) (ns k)))
        Filter.atTop (𝓝 ε) →
      let η := ε + Real.logb (1 / γ) (1 - γ)
      let c := (1 - γ) ^ (rho γ θ)
      ∀ t : ℝ, ContinuousAt (fun z => (F η (Set.Iic z)).toReal) (t / c) →
        Filter.Tendsto
          (fun k => (P {ω | (ns k : ℝ) ^ (-(rho γ θ)) *
            ((passage X (ns k) ω).toNat : ℝ) ≤ t}).toReal)
          Filter.atTop (𝓝 ((F η (Set.Iic (t / c))).toReal))) := by sorry

end SolomonRWRE.SlowApproach
