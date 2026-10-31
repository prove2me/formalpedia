-- Prove2me | Theorems.Thm_OrgAnalytics_eq_A9_two_point
-- name    : OrgAnalytics.eq_A9_two_point
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:09:33.200986+00:00
-- url     : https://prove2.me/theorems/d162c80a-61b1-4438-b23d-259e8da0221c
-- title:
--   Eq. (A.9), p. 48 — the two-point policy on $\{0,(1-\lambda)\Delta\}$ attains $\underline\alpha(\lambda)$ with $\tau=1$ and zero expected tampering cost (corrected: no Assumption 1; $\alpha_H$ of (1))
-- statement:
--   Let $0<\mu<q_H<1$ and $\Delta>0$, and let $1/(2-q_H)\le\lambda<1$. Let $F_\lambda$ be the distribution supported on $\{0,(1-\lambda)\Delta\}$ with
--
--   $$
--   \Pr[c=0]=\frac{p(\lambda)-p^C_S}{p(\lambda)} .
--   $$
--
--   Then $F_\lambda$ is a cost distribution, and for either task allocation it has a designer-optimal outcome with type-I error $\underline\alpha(\lambda)$, approval probability $\tau=1$ after an unaudited recommendation, tampering probability exactly $\Pr[c=0]$, and zero expected tampering cost.
--
--   In this outcome the agent tampers only at cost $0$. This is the policy from which the optimal policy of Proposition 7 is obtained at $\lambda=1/(2-q_H)$.
--
--   Differences from the source:
--   - correction: (1) prints α_H with denominator q_H(1−q_H), a product → α_H = µ(1−q_H)/((1−µ)q_H), the denominator being the odds q_H/(1−q_H); reason: counterexample: at µ = 1/4, q_H = 3/8 the printed form is 64/45 > 1, not a probability; the sentence before (1) sets the posterior to q_H, which solves to the Lean value, and (2) needs it
--   - correction: Assumption 1 holds throughout (p. 13) → F_λ is a cost distribution without Assumption 1; reason: F_λ has no mass above (1−λ)Δ, so F̄((1−λ)Δ) = 0: the paper's own (A.9) violates Assumption 1
--   - generalization: 1/(2−q_H) < λ < 1 and k = S → 1/(2−q_H) ≤ λ < 1 and either task allocation; reason: the printed case is included; expected tampering cost is 0, so integration changes nothing, and the proof of Proposition 7 uses the endpoint
--   - reading: the designer picks any finite experiment and play is weak perfect Bayesian (pp. 9, 12) → the designer picks a status-quo experiment π_S(α); reason: the paper poses the organizational-design problem over status-quo experiments after Proposition 2 (p. 15), and its proofs of Propositions 6 and 7 work there; Propositions 1–2 are not modelled
--   - generalization: α ranges over the set A of (5) → α ranges over [0, 1]; reason: A ⊆ [0, 1]; an α outside A has only continuations the designer strictly improves on or that pay 0, so the designer maximum is the one over A
--   - correction: each π_S(α) has "the unique continuation equilibrium", given by (6)–(7) (p. 14) → IsContEq allows every continuation equilibrium, with ties F_<(g) ≤ t ≤ F_≤(g) and free mixing at posterior q_H, and the designer selects one; reason: counterexample: µ = 1/4, q_H = 3/8, Δ = 1, λ = 8/13, F = F*_opt, α = 0: every τ ∈ (0, 1] with t = 5/9 is a continuation equilibrium; with atoms (6) may also have no solution
--   - reading: reporting and decisions off the tampering margin are equilibrium play in (7) and footnote 18 → after s = H the agent reports H; the principal keeps d_S after an audited s = S and after an unaudited m = S; these are fixed in Outcome; reason: (7) and footnote 18 state this play for status-quo experiments; fixing it removes the off-path beliefs Assumption 1 was introduced to tie down
--   - reading: a common prior µ with µ < q_H (p. 9) → 0 < µ < q_H < 1; reason: at µ = 0, α_H = 0 and every λ gives q_H, so the optimal audit is not pinned down; µ > 0 also makes every posterior well defined
--   - encoding: a distribution function F of the cost c, on [0, ∞) → a probability measure on ℝ with no mass below 0; F(c) is massLE F c; reason: same objects; atoms are kept, as the paper needs them
-- source:
--   Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), doi:10.1287/mnsc.2023.00207, proof of Proposition 6(ii), eq. (A.9), p.48 (PDF 50)

import Mathlib
import Definitions.Def_OrgAnalytics_Model

open MeasureTheory

namespace OrgAnalytics

/-- **The two-point policy (A.9).** For `1/(2 − q_H) ≤ λ < 1` and either task allocation, the
distribution on `{0, (1 − λ) Δ}` with `Pr[c = 0] = (p(λ) − p^C_S)/p(λ)` is a cost distribution
with a designer-optimal outcome that has type-I error `α(λ)`, rubber-stamping `τ = 1`, tampering
probability exactly `Pr[c = 0]`, and zero expected tampering cost.
Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), proof of
Proposition 6(ii), eq. (A.9), p.48 (PDF 50).

**Formalization Note** The paper's `k` is `S`, and `λ > 1/(2 − q_H)`; the endpoint is the case its
proof of Proposition 7 uses. Both task allocations hold because the cost is zero. -/
theorem eq_A9_two_point (P : Params) (k : TaskAlloc) {lam : ℝ} (hlo : P.lamStar ≤ lam)
    (h1 : lam < 1) :
    IsCostDist (P.FA9 lam) ∧
      ∃ o, P.IsDesignerOpt k lam (P.FA9 lam) o ∧ o.α = P.alphaLower lam ∧
        o.t = (P.pLower lam - P.pCS) / P.pLower lam ∧ o.τ = 1 ∧
        P.tamperingCost lam (P.FA9 lam) o = 0 := by sorry

end OrgAnalytics
