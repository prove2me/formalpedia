-- Prove2me | Theorems.Thm_SolomonRWRE_SlowApproach_lemma_2_10
-- name    : SolomonRWRE.SlowApproach.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:14.330604+00:00
-- url     : https://prove2.me/theorems/ab82f413-26df-4117-9085-5c572204655a
-- title:
--   Lemma (2.10) — limits of passage times to successive mirrors
-- statement:
--   Let $T_{V_n}$ be the time at which the random walk first reaches its $n$th one-way mirror. If $\gamma\theta=1$, then
--   $$
--   \frac{T_{V_n}}{2n\log_\theta n}\xrightarrow{P}\frac{\theta}{\theta-1}.
--   $$
--   If $\gamma\theta>1$ and $n_k\to\infty$ with $\{\log_{1/\gamma}n_k\}\to\varepsilon$, the laws of $n_k^{-\rho}T_{V_{n_k}}$ converge to $F_\varepsilon$, whose Laplace transform is (2.12). The distributional clause is tested at continuity points of the limiting distribution function.
--
--   This lemma gives the mirror-indexed passage-time limits used to pass to ordinary sites.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 14, Lemma (2.10), displays (2.11)–(2.12)

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology

namespace SolomonRWRE.SlowApproach

/-- Solomon, Lemma (2.10), p. 14, both clauses. `F` is the family of nonnegative
laws uniquely specified by Laplace transform (2.12). -/
theorem lemma_2_10 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ)
    (γ θ : ℝ) (h : IsMirrorEnvironment P α X γ θ) :
    (γ * θ = 1 →
      MeasureTheory.TendstoInMeasure P
        (fun n ω => ((passage X (mirrorPos α n ω) ω).toNat : ℝ) /
          (2 * (n : ℝ) * Real.logb θ n)) Filter.atTop
        (fun _ => θ / (θ - 1))) ∧
    (1 < γ * θ → ∀ (F : ℝ → MeasureTheory.Measure ℝ),
      IsLimitLaw F γ θ → ∀ (ns : ℕ → ℕ) (ε : ℝ),
      Filter.Tendsto ns Filter.atTop Filter.atTop →
      Filter.Tendsto (fun k => Int.fract (Real.logb (1 / γ) (ns k)))
        Filter.atTop (𝓝 ε) →
      ∀ t : ℝ, ContinuousAt (fun z => (F ε (Set.Iic z)).toReal) t →
        Filter.Tendsto
          (fun k => (P {ω | (ns k : ℝ) ^ (-(rho γ θ)) *
            ((passage X (mirrorPos α (ns k) ω) ω).toNat : ℝ) ≤ t}).toReal)
          Filter.atTop (𝓝 ((F ε (Set.Iic t)).toReal))) := by sorry

end SolomonRWRE.SlowApproach
