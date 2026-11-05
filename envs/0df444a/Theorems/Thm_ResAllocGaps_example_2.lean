-- Prove2me | Theorems.Thm_ResAllocGaps_example_2
-- name    : ResAllocGaps.example_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:08.109213+00:00
-- url     : https://prove2.me/theorems/e43ef68f-07e7-4810-8aff-a2151fcf09c8
-- title:
--   Example 2 — a law with density $f\ge\alpha_0>0$ on $[0,1]$ is $(0,1,0)$-clustered with $C=1/\alpha_0$
-- statement:
--   Let $\mu$ be a probability law on $[0,1]$ with a (measurable) density $f$, and suppose there is $\alpha_0>0$ with $f(x)\ge\alpha_0$ for all $x\in[0,1]$. Then $\mu$ is $(\beta=0,\varepsilon_0=1,\delta=0)$-clustered with $n=0$ gaps, and its generalized inverse is $1$-Hölder on $(0,1]$ with constant $C=1/\alpha_0$:
--   $$|F^{-1}(q)-F^{-1}(q')|\le\frac{1}{\alpha_0}\,|q-q'|\qquad(q,q'\in(0,1]).$$
--   The uniform law on $[0,1]$ is the case $f\equiv1$; since its single cluster has size $1\ge\tfrac12$, it lies in $\mathscr F_{0,1/2}$, the class of the goal at $\beta=0$.
--
--   Differences from the source:
--   - generalization: the non-atomic distributions with pdf f of Bray (2022), Assumption 2, with f ≥ α₀ on [0, 1] → every probability law on [0, 1] with a measurable density f ≥ α₀ on [0, 1]; reason: the conclusion uses only the lower bound on the density; Bray's distributions are among these, so the statement specializes to the page
--   - encoding: (β = 0, ε₀ = 1, δ = 0)-clustered with n = 0 gaps, i.e. F⁻¹ 1-Hölder on (0, 1] with C = 1/α₀ → IsClustered μ 0 1 0 and the explicit bound with 1/α₀; reason: same content
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, §3.1, p.12, Example 2

import Mathlib
import Definitions.Def_ResAllocGaps_quantile
import Definitions.Def_ResAllocGaps_IsClustered

open MeasureTheory ProbabilityTheory

namespace ResAllocGaps

/-- **Example 2 (Non-atomic distributions with contiguous support)**, Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, p.12: a candidate-ability law on `[0, 1]` with pdf `f` such that
`f(x) ≥ α₀ > 0` for all `x ∈ [0, 1]` is `(β = 0, ε₀ = 1, δ = 0)`-clustered with `n = 0` gaps,
i.e. `F⁻¹` is 1-Hölder continuous over `(0, 1]` with the constant `C = 1/α₀`.

**Formalization Note.** The law is `μ = f · Lebesgue` (`withDensity` of `ENNReal.ofReal ∘ f`) with
`f` measurable, a probability measure with `μ([0, 1]) = 1` (abilities lie in `[0, 1]`, p.11). The
second clause is the `C = 1/α₀` bound on `(0, 1]`. The uniform law is the case `f ≡ 1`. -/
theorem example_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hf : Measurable f)
    (hμf : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hμ : μ (Set.Icc 0 1) = 1) (α₀ : ℝ) (hα₀ : 0 < α₀)
    (hfα : ∀ x ∈ Set.Icc (0 : ℝ) 1, α₀ ≤ f x) :
    IsClustered μ 0 1 0 ∧
      ∀ q ∈ Set.Ioc (0 : ℝ) 1, ∀ q' ∈ Set.Ioc (0 : ℝ) 1,
        |quantile μ q - quantile μ q'| ≤ 1 / α₀ * |q - q'| := by sorry

end ResAllocGaps
