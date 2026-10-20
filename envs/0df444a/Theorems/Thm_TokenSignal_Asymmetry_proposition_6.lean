-- Prove2me | Theorems.Thm_TokenSignal_Asymmetry_proposition_6
-- name    : TokenSignal.Asymmetry.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:55.921926+00:00
-- url     : https://prove2.me/theorems/ebfecb16-0705-4273-b9b6-3bd1a80b559b
-- title:
--   Proposition 6: the signaling-advantage windows
-- statement:
--   Fix high-type expected payoff $\mu_H$, investment $I$, cost $C$, risk aversion $\gamma$, and, for each clause, the parameter not being varied. There are thresholds $\mu_l<\mu_u$ and $\sigma_l<\sigma_u$ such that token financing permits separation while equity financing does not exactly when the varied low-type mean or volatility lies in its respective window:
--
--   $$\text{token signaling advantage}\iff\mu_l\le\mu_L<\mu_u,\qquad\text{token signaling advantage}\iff\sigma_l\le\sigma<\sigma_u.$$
--
--   The low-type mean ranges over $4(I+C)\le\mu_L<\mu_H$, and volatility ranges over $\sigma>0$. The result identifies moderate heterogeneity and moderate volatility as the parameter regimes in which tokens alone support a separating equilibrium.
--
--   **Formalization Note** “Signaling advantage” means that a separating equilibrium exists with tokens and none exists with equity. The two biconditionals are separate comparative statics. The standing domain includes $C>0$ and low-type financing feasibility.
-- source:
--   Chod & Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (version of Dec. 14, 2019), p. 22 (PDF 23), Proposition 6

import Mathlib
import Definitions.Def_TokenSignal_Asymmetry_Model

namespace TokenSignal.Asymmetry

theorem proposition_6 (P : Params) (hS : P.Standing) :
    (∃ μl μu : ℝ, μl < μu ∧ ∀ μL' : ℝ,
      4 * (P.I + P.C) ≤ μL' → μL' < P.μH →
        (SignalingAdvantage { P with μL := μL' } ↔ μl ≤ μL' ∧ μL' < μu)) ∧
    (∃ σl σu : ℝ, σl < σu ∧ ∀ σ' : ℝ, 0 < σ' →
        (SignalingAdvantage { P with σ := σ' } ↔ σl ≤ σ' ∧ σ' < σu)) := by sorry
end TokenSignal.Asymmetry
