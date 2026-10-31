-- Prove2me | Theorems.Thm_SuperPareto_lemma_1
-- name    : SuperPareto.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:23.242086+00:00
-- url     : https://prove2.me/theorems/e9e4d53b-bb6e-4c3e-ab00-db73fc63e87e
-- title:
--   Lemma 1, p.9 — WNAID variables pull back through an increasing convex $f$
-- statement:
--   Let $X_1,\dots,X_n$ be weakly negatively associated real random variables, let $\mu$ be a probability law on $\mathbb R$ (the law of a random variable $Y$), and let $f:\mathbb R\to\mathbb R$ be increasing and convex with $X_i\overset{d}{=}f(Y)$ for every $i$. Then there is a probability law $\nu$ on $\mathbb R^n$, the joint law of random variables $(Y_1,\dots,Y_n)$, such that
--
--   1. $Y_1,\dots,Y_n$ are weakly negatively associated under $\nu$;
--   2. each $Y_i$ has law $\mu$, i.e. $Y_i\overset{d}{=}Y$;
--   3. $(f(Y_1),\dots,f(Y_n))\overset{d}{=}(X_1,\dots,X_n)$.
--
--   So a WNAID family of transforms $f(\cdot)$ of a common law can be written as the transform of a WNAID family with that law. With $Y\sim\mathrm{Pareto}(1)$ this reduces Theorem 1(i) for super-Pareto variables to the Pareto(1) case. The lemma does not assume super-Pareto laws: $Y$ is arbitrary and $f$ may be constant.
--
--   **Formalization Note** The conclusion is stated for the joint law $\nu$ on $\iota\to\mathbb R$, whose coordinate maps are the $Y_i$. On the paper's atomless probability space every Borel law on $\mathbb R^n$ is the law of a random vector, so this gives the printed statement there.
--
--   Differences from the source:
--   - reading: there exist WNAID random variables Y₁, …, Yₙ with Y₁ =d Y and (X₁, …, Xₙ) =d (f(Y₁), …, f(Yₙ)) → there exists a probability measure ν on ι → ℝ whose coordinates are weakly negatively associated, each with law μ, and whose image under y ↦ (f(yᵢ))ᵢ is the joint law of (Xᵢ); reason: the coordinates of (ℝ^ι, ν) are such random variables; on the paper's atomless space every Borel law on ℝⁿ is realized by a random vector, so the two statements coincide there
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S; as a hypothesis this quantifies over fewer sets, so the theorem is at least as strong
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: X =d f(Y), X₁ =d X, X₁, …, Xₙ WNAID → `IsWNA P X` and P.map (X i) = μ.map f for every i, with μ the law of Y; reason: identical laws of the Xᵢ together with X₁ =d X =d f(Y) say exactly that every Xᵢ has law μ.map f; only the law of Y enters the statement
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Lemma 1, p.9 (proof in Appendix A, p.13)

import Mathlib
import Definitions.Def_SuperPareto_IsWNA

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Lemma 1: pulling WNAID variables back through `f`.** Chen, Embrechts, Wang, *An unexpected
stochastic dominance*, arXiv:2208.08471v4, Lemma 1, p.9: suppose that `X =d f(Y)` for an
increasing convex function `f`, `X₁ =d X`, and `X₁, …, Xₙ` are WNAID. There exist WNAID random
variables `Y₁, …, Yₙ` with `Y₁ =d Y` such that `(X₁, …, Xₙ) =d (f(Y₁), …, f(Yₙ))`.

Here `μ` is the law of `Y` (any probability measure on `ℝ`), every `Xᵢ` has law `μ.map f`, and the
conclusion is a probability measure `ν` on `ι → ℝ`, the joint law of `(Y₁, …, Yₙ)`: its coordinate
maps are weakly negatively associated under `ν`, each has law `μ`, and the image of `ν` under
`y ↦ (f(y₁), …, f(yₙ))` is the joint law of `(X₁, …, Xₙ)`.

**Formalization Note.** The conclusion is stated for the joint law: the random variables
`Y₁, …, Yₙ` are the coordinates of `(ι → ℝ, ν)`. On the paper's atomless probability space every
Borel law on `ℝⁿ` is the law of some random vector, so this gives the printed statement there; the
atomless assumption itself is not needed. `Y` is an arbitrary random variable and `f` may be
constant, as in the paper (the lemma "does not assume super-Pareto distributions", p.9). -/
theorem lemma_1 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hWNA : IsWNA P X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ) (hfmono : Monotone f)
    (hfconv : ConvexOn ℝ Set.univ f) (hlaw : ∀ i, P.map (X i) = μ.map f) :
    ∃ ν : Measure (ι → ℝ), IsProbabilityMeasure ν ∧ IsWNA ν (fun i y => y i) ∧
      (∀ i, ν.map (fun y => y i) = μ) ∧
      ν.map (fun y i => f (y i)) = P.map (fun ω i => X i ω) := by sorry

end SuperPareto
