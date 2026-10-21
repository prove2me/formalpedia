-- Prove2me | Theorems.Thm_RecallTesting_Duopoly_corollary_3
-- name    : RecallTesting.Duopoly.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:42.603267+00:00
-- url     : https://prove2.me/theorems/9e84cf22-11f7-4515-8ce6-267f28a32c92
-- title:
--   Corollary 3, p. 18 — a dual-firm-test equilibrium needs ρ ≥ ρ̃st, and ρ̃st − ρ̃nt > 0 (closed form)
-- statement:
--   Assume the standing assumptions $V,B,\rho>0$, $\delta\in(0,1]$, $\gamma,\theta\in(0,1)$. Then:
--
--   1. if for some failure probability $\theta'\in(0,1)$ (all other parameters unchanged) both firms testing is an equilibrium of the testing game, then $\rho\ge\tilde\rho^{st}$;
--   2. the two recall-cost thresholds differ by
--   $$\tilde\rho^{st}-\tilde\rho^{nt}=\frac{2(V+B)\Big((3V+4B)\sqrt{VB(5-\gamma)\gamma}+2B(V+B)(3+\gamma)(1-\delta)\Big)}{(3V+4B)^2(3+\gamma)};$$
--   3. in particular $\tilde\rho^{nt}<\tilde\rho^{st}$.
--
--   So the recall costs that support both firms testing lie strictly above those that support neither firm testing.
--
--   **Formalization Note** "For the dual-firm-test equilibrium to exist" is read as existence at some $\theta'\in(0,1)$, which also covers the given $\theta$. The identity in item 2 is the display of the paper's proof of Corollary 3 (p. 38).
-- source:
--   Kim, Koenigsberg & Ofek, I Don’t “Recall”, SSRN working paper 3492105 (Nov. 2019), p. 18 (PDF 19), Corollary 3; proof p. 38 (PDF 39)

import Mathlib
import Definitions.Def_RecallTesting_Duopoly_Model

namespace RecallTesting.Duopoly

theorem corollary_3 (P : Params) (hS : P.Standing) :
    ((∃ θ' : ℝ, 0 < θ' ∧ θ' < 1 ∧ IsNE { P with θ := θ' } true true) → rhoST P ≤ P.ρ) ∧
    rhoST P - rhoNT P =
      2 * (P.V + P.B) * ((3 * P.V + 4 * P.B) * Real.sqrt (P.V * P.B * (5 - P.γ) * P.γ)
          + 2 * P.B * (P.V + P.B) * (3 + P.γ) * (1 - P.δ))
        / ((3 * P.V + 4 * P.B) ^ 2 * (3 + P.γ)) ∧
    rhoNT P < rhoST P := by sorry

end RecallTesting.Duopoly
