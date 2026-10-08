-- Prove2me | Theorems.Thm_SolomonRWRE_SlowApproach_theorem_2_20
-- name    : SolomonRWRE.SlowApproach.theorem_2_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:04.041397+00:00
-- url     : https://prove2.me/theorems/ea9188b6-7ea7-4e61-8359-88bfa2a3e586
-- title:
--   Theorem (2.20) — critical speed and supercritical subsequential laws
-- statement:
--   Consider Solomon’s nearest-neighbour walk in the i.i.d. one-way-mirror environment: $\alpha_j=1$ with probability $1-\gamma$ and $\alpha_j=(1+\theta)^{-1}$ with probability $\gamma$, where $\theta>1$, $0<\gamma<1$, and $\gamma\theta\ge1$.
--
--   If $\gamma\theta=1$, then
--   $$
--   \frac{X_n}{n/\log_\theta n}\xrightarrow{P}\frac12.
--   $$
--   If $\gamma\theta>1$ and $n_k\to\infty$ with $\{\log_\theta n_k\}\to\varepsilon$, then for each $x>0$,
--   $$
--   P\{n_k^{-1/\rho}X_{n_k}<x\}\longrightarrow 1-F_{\lambda(x)}\!\left(((1-\gamma)x)^{-\rho}\right),
--   $$
--   where $\rho=\log_{1/\gamma}\theta$, $\lambda(x)=\varepsilon+\log_{1/\gamma}((1-\gamma)x)$, and $F_\varepsilon$ is the law with Laplace transform (2.12).
--
--   The first clause gives the logarithmically slowed critical growth; the second records the phase-dependent subsequential laws. **Formalization Note** The family $F$ is assumed to consist of probability laws on $[0,\infty)$ with exactly the stated Laplace transforms. The paper’s fractional part in this theorem uses $\log_\theta$, unlike Lemma (2.10).
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 19, Theorem (2.20)

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology

namespace SolomonRWRE.SlowApproach

/-- Solomon, Theorem (2.20), p. 19, both clauses. Formalization Note: the phase in
part (ii) is the fractional part of `log_θ nₖ`, as printed, not `log_(1/γ) nₖ`. -/
theorem theorem_2_20 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ)
    (γ θ : ℝ) (h : IsMirrorEnvironment P α X γ θ) :
    (γ * θ = 1 →
      MeasureTheory.TendstoInMeasure P
        (fun n ω => (X n ω : ℝ) / ((n : ℝ) / Real.logb θ n))
        Filter.atTop (fun _ => (1 / 2 : ℝ))) ∧
    (1 < γ * θ → ∀ (F : ℝ → MeasureTheory.Measure ℝ),
      IsLimitLaw F γ θ → ∀ (ns : ℕ → ℕ) (ε : ℝ),
      Filter.Tendsto ns Filter.atTop Filter.atTop →
      Filter.Tendsto (fun k => Int.fract (Real.logb θ (ns k)))
        Filter.atTop (𝓝 ε) →
      ∀ x : ℝ, 0 < x →
        Filter.Tendsto
          (fun k => (P {ω | (ns k : ℝ) ^ (-(1 / rho γ θ)) *
            (X (ns k) ω : ℝ) < x}).toReal)
          Filter.atTop
          (𝓝 (1 - (F (ε + Real.logb (1 / γ) ((1 - γ) * x))
            (Set.Iic (((1 - γ) * x) ^ (-(rho γ θ))))).toReal))) := by sorry

end SolomonRWRE.SlowApproach
