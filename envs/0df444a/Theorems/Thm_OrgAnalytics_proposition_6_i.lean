-- Prove2me | Theorems.Thm_OrgAnalytics_proposition_6_i
-- name    : OrgAnalytics.proposition_6_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:28.702044+00:00
-- url     : https://prove2.me/theorems/74fa6efd-45de-44cf-acd4-bae18a63b982
-- title:
--   Proposition 6(i), p. 24 — the type-I error is at least $\underline\alpha(\lambda)$, for every prevention policy (corrected: $\alpha_H$ of (1))
-- statement:
--   Let $0<\mu<q_H<1$ and $\Delta>0$. For every audit intensity $0<\lambda\le1$, every task allocation and every cost distribution $F$, every designer-optimal outcome has type-I error
--
--   $$
--   \alpha\ \ge\ \underline\alpha(\lambda)=\frac{2\lambda-1}{\lambda}\,\alpha_H-\frac{\mu(1-\lambda)}{(1-\mu)\lambda}.
--   $$
--
--   The bound does not depend on $F$: no prevention policy can induce an experiment more informative than this at audit intensity $\lambda$.
--
--   Differences from the source:
--   - correction: (1) prints α_H with denominator q_H(1−q_H), a product → α_H = µ(1−q_H)/((1−µ)q_H), the denominator being the odds q_H/(1−q_H); reason: counterexample: at µ = 1/4, q_H = 3/8 the printed form is 64/45 > 1, not a probability; the sentence before (1) sets the posterior to q_H, which solves to the Lean value, and (2) needs it
--   - generalization: 1/(2−q_H) < λ < 1 and separated tasks → 0 < λ ≤ 1 and either task allocation; reason: the printed case is the instance λ in that range with k = S
--   - generalization: Assumption 1, F̄((1−λ)Δ) > 0, holds throughout the paper (p. 13) → not assumed; the statement covers every cost distribution; reason: a bound over a larger class implies the bound over the class with Assumption 1
--   - reading: the designer picks any finite experiment and play is weak perfect Bayesian (pp. 9, 12) → the designer picks a status-quo experiment π_S(α); reason: the paper poses the organizational-design problem over status-quo experiments after Proposition 2 (p. 15), and its proofs of Propositions 6 and 7 work there; Propositions 1–2 are not modelled
--   - generalization: α ranges over the set A of (5) → α ranges over [0, 1]; reason: A ⊆ [0, 1]; an α outside A has only continuations the designer strictly improves on or that pay 0, so the designer maximum is the one over A
--   - correction: each π_S(α) has "the unique continuation equilibrium", given by (6)–(7) (p. 14) → IsContEq allows every continuation equilibrium, with ties F_<(g) ≤ t ≤ F_≤(g) and free mixing at posterior q_H, and the designer selects one; reason: counterexample: µ = 1/4, q_H = 3/8, Δ = 1, λ = 8/13, F = F*_opt, α = 0: every τ ∈ (0, 1] with t = 5/9 is a continuation equilibrium; with atoms (6) may also have no solution
--   - reading: reporting and decisions off the tampering margin are equilibrium play in (7) and footnote 18 → after s = H the agent reports H; the principal keeps d_S after an audited s = S and after an unaudited m = S; these are fixed in Outcome; reason: (7) and footnote 18 state this play for status-quo experiments; fixing it removes the off-path beliefs Assumption 1 was introduced to tie down
--   - reading: a common prior µ with µ < q_H (p. 9) → 0 < µ < q_H < 1; reason: at µ = 0, α_H = 0 and every λ gives q_H, so the optimal audit is not pinned down; µ > 0 also makes every posterior well defined
--   - encoding: a distribution function F of the cost c, on [0, ∞) → a probability measure on ℝ with no mass below 0; F(c) is massLE F c; reason: same objects; atoms are kept, as the paper needs them
-- source:
--   Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), doi:10.1287/mnsc.2023.00207, Proposition 6(i), eq. (17), p.24 (PDF 26); proof pp.46–47 (PDF 48–49)

import Mathlib
import Definitions.Def_OrgAnalytics_Model

open MeasureTheory

namespace OrgAnalytics

/-- **Proposition 6(i): the lower bound on the type-I error.** For every audit intensity
`0 < λ ≤ 1`, every task allocation and every prevention policy, the designer's type-I error is at
least `α(λ) = ((2λ − 1)/λ) α_H − µ(1 − λ)/((1 − µ) λ)`.
Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), Proposition 6(i),
eq. (17), p.24 (PDF 26).

**Formalization Note** The paper states it for `1/(2 − q_H) < λ < 1` and separation; this covers
that case. -/
theorem proposition_6_i (P : Params) (k : TaskAlloc) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1)
    {F : Measure ℝ} (hF : IsCostDist F) {o : Outcome} (ho : P.IsDesignerOpt k lam F o) :
    P.alphaLower lam ≤ o.α := by sorry

end OrgAnalytics
