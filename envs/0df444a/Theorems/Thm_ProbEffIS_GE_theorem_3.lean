-- Prove2me | Theorems.Thm_ProbEffIS_GE_theorem_3
-- name    : ProbEffIS.GE.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:48.425984+00:00
-- url     : https://prove2.me/theorems/4c6457fe-6d92-401f-bd85-635f2880fe60
-- title:
--   Theorem 3 — sufficient conditions for strong probabilistic efficiency
-- statement:
--   Split each rare event into disjoint parts $A_{1,\gamma}$ and $A_{2,\gamma}$, with original probabilities $p_1,p_2$ and $p=p_1+p_2\to0$. Let $Z_1$ and $Z$ be the corresponding importance-sampling outputs under $\widetilde P_\gamma$, and write $\widetilde p_2=\widetilde P_\gamma(A_{2,\gamma})$. Suppose $p_1/p\to1$, a single sample size $n\ge1$ grows subexponentially in $-\log p$ and satisfies $\widetilde{\operatorname{Var}}(Z_1)/(np_1^2)\to0$, and $n\widetilde p_2\to0$. Then, for every $\varepsilon>0$, eventually
--
--   $$
--   \delta_\varepsilon(\hat p,p)\le\sqrt{\frac{\widetilde{\operatorname{Var}}(Z_1)}{np_1^2(\varepsilon-n\widetilde p_2)}}+\frac{p_2}{p}\longrightarrow0,
--   $$
--
--   and $Z$ is strongly probabilistically efficient. This criterion combines a well-controlled main region with a sufficiently rare omitted region.
--
--   **Formalization Note** The variance is a finite $L^2$ variance eventually. The displayed bound is asserted eventually, when its denominator is positive. The paper’s premise of an asymptotically efficient estimator of $p_1$ is represented by the sample size and variance conclusion that it supplies.
-- source:
--   Bai, Huang, Lam & Zhao, Over-Conservativeness of Variance-Based Efficiency Criteria and Probabilistic Efficiency in Rare-Event Simulation, arXiv:2110.12573v2, pp. 17–18, Theorem 3

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory

namespace ProbEffIS.GE

/-- Theorem 3, pp. 17–18: a negligible omitted region and controlled variance imply
    strong probabilistic efficiency, with the paper's explicit discrepancy bound. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ℝ → Measure Ω) [∀ γ, IsProbabilityMeasure (P γ)]
    (hQ : ∀ᶠ γ in atTop, IsProbabilityMeasure (Q γ))
    (A₁ A₂ : ℝ → Set Ω)
    (hA₁ : ∀ γ, MeasurableSet (A₁ γ))
    (hA₂ : ∀ γ, MeasurableSet (A₂ γ))
    (hdisj : ∀ γ, Disjoint (A₁ γ) (A₂ γ))
    (hac : ∀ γ, (P γ).restrict (A₁ γ ∪ A₂ γ) ≪ Q γ)
    (hp : Tendsto (eventProb P (fun γ => A₁ γ ∪ A₂ γ)) atTop (𝓝 0))
    (c1 : Tendsto
      (fun γ => eventProb P A₁ γ / eventProb P (fun t => A₁ t ∪ A₂ t) γ)
      atTop (𝓝 1))
    (n : ℝ → ℕ) (hn : ∀ γ, 1 ≤ n γ)
    (hnsub : IsSubexpIn (fun γ => (n γ : ℝ))
      (fun γ => -Real.log (eventProb P (fun t => A₁ t ∪ A₂ t) γ)))
    (hL2 : ∀ᶠ γ in atTop, MemLp (eventOutput P Q A₁ γ) 2 (Q γ))
    (c2 : Tendsto
      (fun γ => variance (eventOutput P Q A₁ γ) (Q γ) /
        ((n γ : ℝ) * (eventProb P A₁ γ) ^ 2)) atTop (𝓝 0))
    (c3 : Tendsto
      (fun γ => (n γ : ℝ) * eventProb Q A₂ γ) atTop (𝓝 0)) :
    (∀ ε : ℝ, 0 < ε →
      (∀ᶠ γ in atTop,
        minRelDisc (Q γ) (n γ)
          (eventOutput P Q (fun t => A₁ t ∪ A₂ t) γ)
          (eventProb P (fun t => A₁ t ∪ A₂ t) γ) ε ≤
        Real.sqrt (variance (eventOutput P Q A₁ γ) (Q γ) /
          ((n γ : ℝ) * (eventProb P A₁ γ) ^ 2 *
            (ε - (n γ : ℝ) * eventProb Q A₂ γ))) +
          eventProb P A₂ γ / eventProb P (fun t => A₁ t ∪ A₂ t) γ) ∧
      Tendsto (fun γ =>
        Real.sqrt (variance (eventOutput P Q A₁ γ) (Q γ) /
          ((n γ : ℝ) * (eventProb P A₁ γ) ^ 2 *
            (ε - (n γ : ℝ) * eventProb Q A₂ γ))) +
          eventProb P A₂ γ / eventProb P (fun t => A₁ t ∪ A₂ t) γ)
        atTop (𝓝 0)) ∧
    StronglyProbEfficient Q
      (eventOutput P Q (fun t => A₁ t ∪ A₂ t))
      (eventProb P (fun t => A₁ t ∪ A₂ t)) := by sorry

end ProbEffIS.GE
