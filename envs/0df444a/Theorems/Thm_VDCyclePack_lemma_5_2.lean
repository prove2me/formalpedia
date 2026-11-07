-- Prove2me | Theorems.Thm_VDCyclePack_lemma_5_2
-- name    : VDCyclePack.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:06:36.023459+00:00
-- url     : https://prove2.me/theorems/0f3973d2-fdf8-4cf4-8eff-6ec24272a9c1
-- title:
--   Lemma 5.2: $\mathbb E[t\log(t+2)]\le\mu\log(\mu+3)$ for a sum $t$ of independent Bernoulli variables
-- statement:
--   Let $I_1,\dots,I_k$ be independent Bernoulli random variables, let $t=\sum_i I_i$ and $\mu=\mathbb E[t]$. Then
--   $$
--   \mathbb E\bigl[t\log_2(t+2)\bigr]\ \le\ \mu\log_2(\mu+3).
--   $$
--
--   It controls the nonlinear term of the structural bound under the random sample of Lemma 5.1.
--
--   **Formalization Note** The variables are real functions on a probability space, measurable, mutually independent (`iIndepFun`), indexed by a finite type, each taking only the values $0$ and $1$; expectations are Bochner integrals of bounded functions.
--
--   Differences from the source:
--   - encoding: t a sum of independent Bernoulli random variables → finitely many (possibly no) measurable I i : Ω → ℝ on a probability space, iIndepFun, with I i ω ∈ {0, 1} for every ω; t = Σ i, I i; reason: a Bernoulli variable agrees almost surely with a {0,1}-valued one, and changing variables on a null set changes neither independence nor the expectations
--   - encoding: E[·], log → Bochner integrals ∫ … ∂μ of bounded measurable functions; Real.logb 2; reason: the integrands are bounded, so the integrals are the expectations; logs are base two (p.9)
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 5.2, p.16

import Mathlib

namespace VDCyclePack

/-- **Lemma 5.2 (t log t of a sum of independent Bernoulli variables).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 5.2, p.16: "If t is a sum of independent Bernoulli random variables with
E[t] = µ, then E[t log(t + 2)] ≤ µ log(µ + 3)."

Let `I₁, …, I_k` be independent random variables on a probability space, each taking only the
values `0` and `1`, let `t = Σᵢ Iᵢ` and `μ = E[t]`. Then `E[t·log₂(t + 2)] ≤ μ·log₂(μ + 3)`.

**Formalization Note.** The variables are indexed by a finite type (possibly empty, then
`t = μ = 0`); they are measurable, `{0, 1}`-valued and mutually independent (`iIndepFun`).
Logarithms are base two. The integrands are bounded and measurable, so the integrals are genuine
expectations. -/
theorem lemma_5_2 {Ω ι : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] [Fintype ι] (I : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (I i)) (hbern : ∀ i ω, I i ω = 0 ∨ I i ω = 1)
    (hind : ProbabilityTheory.iIndepFun I μ) :
    ∫ ω, (∑ i, I i ω) * Real.logb 2 ((∑ i, I i ω) + 2) ∂μ ≤
      (∫ ω, (∑ i, I i ω) ∂μ) * Real.logb 2 ((∫ ω, (∑ i, I i ω) ∂μ) + 3) := by sorry

end VDCyclePack
