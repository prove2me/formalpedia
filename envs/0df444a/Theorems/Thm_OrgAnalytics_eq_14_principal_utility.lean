-- Prove2me | Theorems.Thm_OrgAnalytics_eq_14_principal_utility
-- name    : OrgAnalytics.eq_14_principal_utility
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:29.213+00:00
-- url     : https://prove2.me/theorems/aa540e1e-f59b-4688-9155-c05368b05e0f
-- title:
--   Eqs. (13)–(14), p. 18 — at every designer-optimal outcome, $U=q_H+\lambda(1-\mu)q_H(\alpha_H-\alpha)$ (corrected: $q$ in (13) is the posterior after $s=H$; $\alpha_H$ of (1))
-- statement:
--   Let $0<\mu<q_H<1$ and $\Delta>0$. Fix a task allocation $k$, an audit intensity $\lambda\in[0,1]$ and a cost distribution $F$, and let $(\alpha,t,\tau,\sigma)$ be a designer-optimal outcome. Write $q=\mu/(\mu+(1-\mu)\alpha)$ for the posterior after a true outcome $s=H$. Then the principal's expected utility $U$ satisfies
--
--   $$
--   U=q_H+\Pr[s=H]\,\lambda\,(q-q_H)=q_H+\lambda(1-\mu)q_H(\alpha_H-\alpha)=q_H+(q_H-\mu)\,\lambda\,\frac{\alpha_H-\alpha}{1-\alpha_H},
--   $$
--
--   where $\Pr[s=H]=\mu+(1-\mu)\alpha$. Moreover, for every threshold $\bar c$ with $\bar F(\bar c)=(1-\alpha_H)/(1-\alpha)$, the first half of (6),
--
--   $$
--   U=q_H+(q_H-\mu)\,\lambda\,\frac{F(\bar c)}{\bar F(\bar c)}.
--   $$
--
--   The principal gains only from audited approvals. So her utility rises with the audit intensity and with the informativeness of the experiment, which is what the rest of the design problem trades off.
--
--   Differences from the source:
--   - correction: (1) prints α_H with denominator q_H(1−q_H), a product → α_H = µ(1−q_H)/((1−µ)q_H), the denominator being the odds q_H/(1−q_H); reason: counterexample: at µ = 1/4, q_H = 3/8 the printed form is 64/45 > 1, not a probability; the sentence before (1) sets the posterior to q_H, which solves to the Lean value, and (2) needs it
--   - correction: (13) calls q the posterior "after an unaudited approval recommendation" → q is the posterior μ/(μ+(1−μ)α) after a true s = H; reason: the unaudited posterior is q_H in equilibrium, which would make (13) read U = q_H; the proof of Proposition 7 has S(π_S(λ)) = {0, q(λ)} and q(λ_opt) = 1
--   - generalization: (14) is stated at the threshold c̄* solving (6) → the closed forms in α hold at every designer-optimal outcome, and (14) for every c with F̄(c) = (1−α_H)/(1−α); reason: with atoms (6) may have no solution; when c̄* solves it the last clause is (14)
--   - generalization: Assumption 1, F̄((1−λ)Δ) > 0, holds throughout the paper (p. 13) → not assumed; the statement covers every cost distribution; reason: a bound over a larger class implies the bound over the class with Assumption 1
--   - reading: the designer picks any finite experiment and play is weak perfect Bayesian (pp. 9, 12) → the designer picks a status-quo experiment π_S(α); reason: the paper poses the organizational-design problem over status-quo experiments after Proposition 2 (p. 15), and its proofs of Propositions 6 and 7 work there; Propositions 1–2 are not modelled
--   - generalization: α ranges over the set A of (5) → α ranges over [0, 1]; reason: A ⊆ [0, 1]; an α outside A has only continuations the designer strictly improves on or that pay 0, so the designer maximum is the one over A
--   - correction: each π_S(α) has "the unique continuation equilibrium", given by (6)–(7) (p. 14) → IsContEq allows every continuation equilibrium, with ties F_<(g) ≤ t ≤ F_≤(g) and free mixing at posterior q_H, and the designer selects one; reason: counterexample: µ = 1/4, q_H = 3/8, Δ = 1, λ = 8/13, F = F*_opt, α = 0: every τ ∈ (0, 1] with t = 5/9 is a continuation equilibrium; with atoms (6) may also have no solution
--   - reading: reporting and decisions off the tampering margin are equilibrium play in (7) and footnote 18 → after s = H the agent reports H; the principal keeps d_S after an audited s = S and after an unaudited m = S; these are fixed in Outcome; reason: (7) and footnote 18 state this play for status-quo experiments; fixing it removes the off-path beliefs Assumption 1 was introduced to tie down
--   - reading: a common prior µ with µ < q_H (p. 9) → 0 < µ < q_H < 1; reason: at µ = 0, α_H = 0 and every λ gives q_H, so the optimal audit is not pinned down; µ > 0 also makes every posterior well defined
--   - encoding: a distribution function F of the cost c, on [0, ∞) → a probability measure on ℝ with no mass below 0; F(c) is massLE F c; reason: same objects; atoms are kept, as the paper needs them
-- source:
--   Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), doi:10.1287/mnsc.2023.00207, eqs. (13)–(14), p.18 (PDF 20)

import Mathlib
import Definitions.Def_OrgAnalytics_Model

open MeasureTheory

namespace OrgAnalytics

/-- **Eqs. (13)–(14): the principal's equilibrium utility.** At every designer-optimal outcome of
every design, for `q` the posterior after `s = H`,
`U = q_H + Pr[s = H] λ (q − q_H)` (13), `U = q_H + λ (1 − µ) q_H (α_H − α)`, and
`U = q_H + (q_H − µ) λ (α_H − α)/(1 − α_H)`; and this is (14),
`U = q_H + (q_H − µ) λ F(c̄)/F̄(c̄)`, for every `c̄` satisfying the first half of (6).
Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), eqs. (13)–(14), p.18
(PDF 20).

**Formalization Note** The text before (13) calls `q` the posterior "after an unaudited approval
recommendation". The formula needs the posterior after a true `s = H`, as in the proof of
Proposition 7 (p.48), `S(π_S(λ)) = {0, q(λ)}`; the unaudited posterior is `q_H` in equilibrium and
would make (13) read `U = q_H`. With atoms (6) may have no solution, so the closed forms in `α`
are stated too. -/
theorem eq_14_principal_utility (P : Params) (k : TaskAlloc) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) {F : Measure ℝ} (hF : IsCostDist F) {o : Outcome}
    (ho : P.IsDesignerOpt k lam F o) :
    P.principalUtility lam o =
        P.qH + (P.mu + (1 - P.mu) * o.α) * lam * (P.posterior o.α - P.qH) ∧
      P.principalUtility lam o = P.qH + lam * (1 - P.mu) * P.qH * (P.alphaH - o.α) ∧
      P.principalUtility lam o =
        P.qH + (P.qH - P.mu) * lam * ((P.alphaH - o.α) / (1 - P.alphaH)) ∧
      ∀ c : ℝ, 1 - massLE F c = (1 - P.alphaH) / (1 - o.α) →
        P.principalUtility lam o =
          P.qH + (P.qH - P.mu) * lam * (massLE F c / (1 - massLE F c)) := by sorry

end OrgAnalytics
