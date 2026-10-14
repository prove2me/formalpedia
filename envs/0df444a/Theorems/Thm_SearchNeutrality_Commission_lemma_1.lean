-- Prove2me | Theorems.Thm_SearchNeutrality_Commission_lemma_1
-- name    : SearchNeutrality.Commission.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:38:30.476215+00:00
-- url     : https://prove2.me/theorems/eca5b776-995b-4602-9e70-f86872d9ea0f
-- title:
--   Lemma 1, p. 25 — at α = 1/2 with search neutrality the unique equilibrium is p_F = p_T = 1, with π_F = ρ_H(1+r)/2 and π_T = ρ_H(1−r)/2
-- statement:
--   Let $0<\rho_L<\rho_H<1$ be the match probabilities, $r\in[0,1)$ the commission, and let the two consumer types have equal mass, $\alpha=1/2$. Suppose search neutrality is in force: $F$ is prominent for type-$f$ consumers and $T$ for type-$t$ consumers.
--
--   Then $(p_F,p_T)=(1,1)$ is a pricing equilibrium, it is the only one, and the equilibrium profits are
--   $$\pi_F^{S*}=\frac{\rho_H(1+r)}{2},\qquad \pi_T^{S*}=\frac{\rho_H(1-r)}{2}.$$
--
--   With neutrality each seller is shown first to the consumers who like its product more, and at equal popularity both sellers extract the full surplus of these consumers. This is the benchmark against which Proposition 5 compares the market without neutrality.
--
--   **Formalization Note** "The equilibrium" is formalized as existence plus "every equilibrium has these prices"; prices range over $[0,1]$ (p. 8). The commission is assumed $r<1$: at $r=1$ the third party's profit is identically $0$, every price is a best reply, and uniqueness fails. The paper does not state the range of $r$; $0\le r<1$ is a disclosed reading.
-- source:
--   Zou & Zhou, Self-Preferencing and Search Neutrality in Online Retail Platforms, authors' manuscript (Management Science, DOI 10.1287/mnsc.2022.01795), p. 25, Lemma 1

import Mathlib
import Definitions.Def_SearchNeutrality_Commission_Model

namespace SearchNeutrality.Commission

/-- Lemma 1, p. 25: at `α = 1/2` with search neutrality, the equilibrium prices are
`p_F = p_T = 1`, with profits `π_F = ρ_H(1+r)/2` and `π_T = ρ_H(1-r)/2`. -/
theorem lemma_1 (ρH ρL r : ℝ) (hL : 0 < ρL) (hLH : ρL < ρH) (hH : ρH < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsSEquilibrium ρH ρL r (1 / 2) 1 1 ∧
    (∀ pF pT : ℝ, IsSEquilibrium ρH ρL r (1 / 2) pF pT → pF = 1 ∧ pT = 1) ∧
    platformProfit ρH ρL r (1 / 2) neutral 1 1 = ρH * (1 + r) / 2 ∧
    sellerProfit ρH ρL r (1 / 2) neutral 1 1 = ρH * (1 - r) / 2 := by sorry

end SearchNeutrality.Commission
