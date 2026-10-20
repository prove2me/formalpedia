-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_proposition_3
-- name    : TimeLockedSales.Reform.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:34.616189+00:00
-- url     : https://prove2.me/theorems/9d84f022-3bd8-4dc0-84fb-c9ee7e5e8570
-- title:
--   Proposition 3, p. 14 — net purchase position determines the platform posterior
-- statement:
--   Under an obedient recommendation policy and in the focus region, consider a proprietary history $H$ of positive probability. Let $N(H)$ count neutral-recommendation purchases minus neutral-recommendation non-purchases. The platform's posterior after that history is
--   $$\mathbb E[V\mid H,\sigma]=v_{N(H)},\qquad v_n=\frac{v_0}{v_0+(1-v_0)((1-q)/q)^n}.$$
--   Thus the history's payoff-relevant information is summarized by one integer. After $t$ customers, $|N(H)|\le t$.
--
--   **Formalization Note.** The displayed quotient is interpreted through the definition's two-sided product expression at $q=1$. A Lean history of length $t$ is the paper's $H_{t+1}$, which accounts for the shifted bound. The posterior is asserted only for a positive-probability history. Obedience refers to Bayesian responses on realized signal–message pairs, resolving the weak-IC endpoint issue.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), p. 14, Proposition 3, (6)–(7); p. 15, (8)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- Proposition 3, p. 14: the posterior depends on the history through (7) alone. -/
theorem proposition_3 (P : Params) (hS : P.Standing) (hR : P.Region)
    (σ : InfoPolicy SignType) (hOb : IsObedient P σ)
    (t : ℕ) (ht : t ≤ P.T) (h : Fin t → SignType × Bool)
    (hpos : 0 < law P σ t true h + law P σ t false h) :
    law P σ t true h / (law P σ t true h + law P σ t false h) =
      vN P (netPos h) ∧ |netPos h| ≤ (t : ℤ) := by sorry

end TimeLockedSales.Reform
