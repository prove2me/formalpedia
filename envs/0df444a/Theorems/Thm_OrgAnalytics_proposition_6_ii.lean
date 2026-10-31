-- Prove2me | Theorems.Thm_OrgAnalytics_proposition_6_ii
-- name    : OrgAnalytics.proposition_6_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:26.237972+00:00
-- url     : https://prove2.me/theorems/99854662-629e-4fc7-a434-1f9c115f6f8b
-- title:
--   Proposition 6(ii), p. 24 — two policies with Assumption 1 attain $\underline\alpha(\lambda)$, and every policy attaining it satisfies (18) (corrected: $\alpha_H$ of (1))
-- statement:
--   Let $0<\mu<q_H<1$ and $\Delta>0$, tasks be separated, and $1/(2-q_H)\le\lambda<1$.
--
--   1. There are two different cost distributions, each satisfying Assumption 1, each with a designer-optimal outcome of type-I error $\underline\alpha(\lambda)$.
--   2. Every cost distribution $F$ with a designer-optimal outcome of type-I error $\underline\alpha(\lambda)$ satisfies
--
--   $$
--   F(c)\ \ge\ \frac{c}{c+\lambda\,\dfrac{p^C_S}{1-p^C_S}\,\Delta}\qquad\text{for }0\le c\le(1-\lambda)\Delta .
--   $$
--
--   So the bound of Proposition 6(i) is attained, not by a unique policy, and attaining it requires low tampering costs to be sufficiently likely.
--
--   Differences from the source:
--   - correction: (1) prints α_H with denominator q_H(1−q_H), a product → α_H = µ(1−q_H)/((1−µ)q_H), the denominator being the odds q_H/(1−q_H); reason: counterexample: at µ = 1/4, q_H = 3/8 the printed form is 64/45 > 1, not a probability; the sentence before (1) sets the posterior to q_H, which solves to the Lean value, and (2) needs it
--   - generalization: 1/(2−q_H) < λ < 1 → 1/(2−q_H) ≤ λ < 1; reason: the printed range is included; the endpoint is the case the proof of Proposition 7 applies
--   - generalization: Assumption 1, F̄((1−λ)Δ) > 0, holds throughout the paper (p. 13) → not assumed; the statement covers every cost distribution in the necessity clause; the two attaining policies do satisfy Assumption 1; reason: a bound over a larger class implies the bound over the class with Assumption 1
--   - encoding: (18) for c ≤ (1−λ)Δ → (18) for 0 ≤ c ≤ (1−λ)Δ; reason: costs are nonnegative, so F(c) = 0 for c < 0
--   - reading: the designer picks any finite experiment and play is weak perfect Bayesian (pp. 9, 12) → the designer picks a status-quo experiment π_S(α); reason: the paper poses the organizational-design problem over status-quo experiments after Proposition 2 (p. 15), and its proofs of Propositions 6 and 7 work there; Propositions 1–2 are not modelled
--   - generalization: α ranges over the set A of (5) → α ranges over [0, 1]; reason: A ⊆ [0, 1]; an α outside A has only continuations the designer strictly improves on or that pay 0, so the designer maximum is the one over A
--   - correction: each π_S(α) has "the unique continuation equilibrium", given by (6)–(7) (p. 14) → IsContEq allows every continuation equilibrium, with ties F_<(g) ≤ t ≤ F_≤(g) and free mixing at posterior q_H, and the designer selects one; reason: counterexample: µ = 1/4, q_H = 3/8, Δ = 1, λ = 8/13, F = F*_opt, α = 0: every τ ∈ (0, 1] with t = 5/9 is a continuation equilibrium; with atoms (6) may also have no solution
--   - reading: reporting and decisions off the tampering margin are equilibrium play in (7) and footnote 18 → after s = H the agent reports H; the principal keeps d_S after an audited s = S and after an unaudited m = S; these are fixed in Outcome; reason: (7) and footnote 18 state this play for status-quo experiments; fixing it removes the off-path beliefs Assumption 1 was introduced to tie down
--   - reading: a common prior µ with µ < q_H (p. 9) → 0 < µ < q_H < 1; reason: at µ = 0, α_H = 0 and every λ gives q_H, so the optimal audit is not pinned down; µ > 0 also makes every posterior well defined
--   - encoding: a distribution function F of the cost c, on [0, ∞) → a probability measure on ℝ with no mass below 0; F(c) is massLE F c; reason: same objects; atoms are kept, as the paper needs them
-- source:
--   Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), doi:10.1287/mnsc.2023.00207, Proposition 6(ii), eq. (18), p.24 (PDF 26); proof, eq. (A.8), p.48 (PDF 50)

import Mathlib
import Definitions.Def_OrgAnalytics_Model

open MeasureTheory

namespace OrgAnalytics

/-- **Proposition 6(ii): many policies attain the bound, all above (18).** Fix
`1/(2 − q_H) ≤ λ < 1` and separation. Two different cost distributions, each satisfying
Assumption 1, have a designer-optimal outcome with type-I error `α(λ)`; and every cost distribution
with such an outcome satisfies
`F(c) ≥ c/(c + λ (p^C_S/(1 − p^C_S)) Δ)` for `0 ≤ c ≤ (1 − λ) Δ`.
Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), Proposition 6(ii),
eq. (18), p.24 (PDF 26); see (A.8), p.48 (PDF 50).

**Formalization Note** The paper's range is `1/(2 − q_H) < λ < 1`; the endpoint is included, which
Proposition 7's proof uses. `F(c)` is the distribution function `massLE F c`. -/
theorem proposition_6_ii (P : Params) {lam : ℝ} (hlo : P.lamStar ≤ lam) (h1 : lam < 1) :
    (∃ F₁ F₂ : Measure ℝ, F₁ ≠ F₂ ∧ IsCostDist F₁ ∧ IsCostDist F₂ ∧
      P.AssumptionOne lam F₁ ∧ P.AssumptionOne lam F₂ ∧
      (∃ o, P.IsDesignerOpt TaskAlloc.S lam F₁ o ∧ o.α = P.alphaLower lam) ∧
      (∃ o, P.IsDesignerOpt TaskAlloc.S lam F₂ o ∧ o.α = P.alphaLower lam)) ∧
    ∀ F : Measure ℝ, IsCostDist F → ∀ o, P.IsDesignerOpt TaskAlloc.S lam F o →
      o.α = P.alphaLower lam → ∀ c ∈ Set.Icc (0 : ℝ) ((1 - lam) * P.Δ),
        c / (c + lam * (P.pCS / (1 - P.pCS)) * P.Δ) ≤ massLE F c := by sorry

end OrgAnalytics
