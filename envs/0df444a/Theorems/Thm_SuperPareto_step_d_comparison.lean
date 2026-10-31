-- Prove2me | Theorems.Thm_SuperPareto_step_d_comparison
-- name    : SuperPareto.step_d_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:30.252756+00:00
-- url     : https://prove2.me/theorems/7b87b6c7-1cf2-4e41-8d88-931b473c45af
-- title:
--   Step (d), p.9 — term-by-term comparison over the events $B_S$
-- statement:
--   Let $X_1,\dots,X_n$ be weakly negatively associated, identically distributed super-Pareto random variables, $X\overset{d}{=}X_1$, $(\theta_1,\dots,\theta_n)\in\Delta_n$, and let $A_1,\dots,A_n$ be events such that the family $(A_1,\dots,A_n)$ is independent of $(X_1,\dots,X_n)$. With $B_S=(\bigcap_{i\in S}A_i)\cap(\bigcap_{i\notin S}A_i^c)$ and $c_S=\sum_{i\in S}\theta_i$, for every $t\in\mathbb R$,
--
--   $$
--   P\Big(\sum_{i=1}^n\theta_iX_i\mathbb 1_{A_i}>t\Big)\ \ge\ \sum_{S\subseteq[n]}P(B_S)\,P(c_SX>t).
--   $$
--
--   When $X$ is independent of the events $B_S$, the right-hand side is $P(\sum_Sc_SX\mathbb 1_{B_S}>t)$, and the inequality is the paper's $\sum_i\theta_iX_i\mathbb 1_{A_i}\ge_{\mathrm{st}}\sum_S\sum_{i\in S}\theta_iX\mathbb 1_{B_S}$, obtained from (4) on each sub-portfolio and the closure of $\le_{\mathrm{st}}$ under mixtures.
--
--   **Formalization Note** "The family is independent of the vector" is `IndepFun` of the vector of indicators $(\mathbb 1_{A_i})_i$ and the vector $(X_i)_i$. Identical distribution is `P.map (X i) = P.map X₀` with $X_0$ the paper's $X$. Probabilities are real (`P.real`).
--
--   Differences from the source:
--   - reading: ∑ᵢθᵢXᵢ𝟙_{Aᵢ} ≥st ∑_S ∑_{i∈S} θᵢX𝟙_{B_S} → P(∑ᵢθᵢXᵢ𝟙_{Aᵢ} > t) ≥ ∑_S P(B_S)·P(c_S X > t) for every t; reason: the printed right-hand side treats X as independent of the B_S, which Theorem 1(ii) does not assume; the two coincide when it is, and the law-level form needs no copy of X
--   - reading: events A₁, …, Aₙ independent of (X₁, …, Xₙ) → the family (𝟙_{A₁}, …, 𝟙_{Aₙ}) jointly independent of the vector (X₁, …, Xₙ); reason: the step uses that each B_S is independent of the vector, which needs joint independence; with each Aᵢ separately independent, Theorem 1(ii) is false (counterexample in MODERATION_NOTES: 7/32 < 8/32)
--   - generalization: X regular (standing assumption of step (d)) → X super-Pareto, regularity not assumed; reason: the comparison uses only (4); the paper's case is a special case
--   - generalization: n ≥ 2 random variables on an atomless probability space (standing assumptions, p.4) → a finite index type ι of any size (n = 1 allowed) on any probability space; reason: the paper's case n ≥ 2 on an atomless space is a special case; for n = 1 the statement holds trivially
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S; as a hypothesis this quantifies over fewer sets, so the theorem is at least as strong
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: X₁, …, Xₙ WNAID (weakly negatively associated and identically distributed) and X =d X₁ → `IsWNA P Xs` and `P.map (Xs i) = P.map X` for every i; reason: identical laws of all Xᵢ together with X =d X₁ is the same as every Xᵢ having the law of X
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (d), p.9, "By (4), ∑i∈S θiXi ≥st ∑i∈S θiX for any S ⊆ [n]. … we have ∑θiXi1Ai = ∑S 1BS ∑i∈S θiXi ≥st ∑S ∑i∈S θiX1BS"

import Mathlib
import Definitions.Def_SuperPareto_IsSuperPareto
import Definitions.Def_SuperPareto_IsWNA

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Step (d): term-by-term comparison over `S ⊆ [n]`.** Chen, Embrechts, Wang, *An unexpected
stochastic dominance*, arXiv:2208.08471v4, §2.3, step (d), p.9: by (4) and closure of first-order
stochastic dominance under mixtures,
`∑ᵢ θᵢ Xᵢ 𝟙_{Aᵢ} = ∑_S 𝟙_{B_S} ∑_{i∈S} θᵢ Xᵢ ≥st ∑_S ∑_{i∈S} θᵢ X 𝟙_{B_S}`.

Stated through survival functions: for WNAID super-Pareto `X₁, …, Xₙ` with `X =d X₁`,
`θ ∈ Δₙ`, and events `A₁, …, Aₙ` whose family is independent of `(X₁, …, Xₙ)`, every `t ∈ ℝ`
satisfies
`P(∑ᵢ θᵢ Xᵢ 𝟙_{Aᵢ} > t) ≥ ∑_{S⊆[n]} P(B_S) · P(c_S X > t)`, with `c_S = ∑_{i∈S} θᵢ`
and `B_S = (⋂_{i∈S} Aᵢ) ∩ (⋂_{i∈Sᶜ} Aᵢᶜ)`.

**Formalization Note.** The paper's right-hand side `∑_S c_S X 𝟙_{B_S}` silently treats `X` as
independent of the `B_S`, which Theorem 1(ii) does not assume; when it is, the right-hand side above
is exactly `P(∑_S c_S X 𝟙_{B_S} > t)` for `t ≥ 0`. "The family `(Aᵢ)` is independent of the vector"
is `IndepFun` of the indicator vector and the vector `(Xᵢ)`. The index set is a `Fintype` `ι`; `Δₙ`
is `stdSimplex ℝ ι`; identical distribution is `P.map (X i) = P.map X₀` for all `i`, with `X₀` the
paper's `X`. Regularity of `X` (the standing assumption of step (d)) is not needed. -/
theorem step_d_comparison {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] (X₀ : Ω → ℝ) (X : ι → Ω → ℝ) (hX₀ : Measurable X₀)
    (hX : ∀ i, Measurable (X i)) (hWNA : IsWNA P X) (hSP : ∀ i, IsSuperPareto P (X i))
    (hID : ∀ i, P.map (X i) = P.map X₀) (θ : ι → ℝ) (hθ : θ ∈ stdSimplex ℝ ι)
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (hAind : IndepFun (fun ω i => (A i).indicator (fun _ => (1 : ℝ)) ω) (fun ω i => X i ω) P)
    (t : ℝ) :
    ∑ S : Finset ι, P.real ((⋂ i ∈ S, A i) ∩ (⋂ (i) (_ : i ∉ S), (A i)ᶜ)) *
        P.real {ω | t < (∑ i ∈ S, θ i) * X₀ ω} ≤
      P.real {ω | t < ∑ i, θ i * (A i).indicator (X i) ω} := by sorry

end SuperPareto
