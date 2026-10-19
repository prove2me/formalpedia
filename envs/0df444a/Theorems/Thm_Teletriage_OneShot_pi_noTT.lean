-- Prove2me | Theorems.Thm_Teletriage_OneShot_pi_noTT
-- name    : Teletriage.OneShot.pi_noTT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:02.648219+00:00
-- url     : https://prove2.me/theorems/6fcd9592-041d-474e-8b3e-079c9ded7b15
-- title:
--   Display, p. 11 (PDF 11) — without teletriage π^ED(b) = 1, π^DD(b) = 0 for b ≥ b0, and both equal b for b < b0
-- statement:
--   In the one-shot open-access model without teletriage, let $\pi^{ED}(b)$ be the probability that a patient with belief $b\in[0,1]$ ends up at the ED and $\pi^{DD}(b)$ the probability that she double-dips (visits the PCP and is then sent on to the ED because she is critical). Under the standing assumptions, for every such $b$,
--   $$\pi^{ED}(b)=\begin{cases}1,&b\ge b_0\\ b,&b<b_0\end{cases}\qquad \pi^{DD}(b)=\begin{cases}0,&b\ge b_0\\ b,&b<b_0.\end{cases}$$
--
--   These are the integrands of the population ED usage and double-dipping rates without teletriage.
--
--   **Formalization Note** $\pi^{ED}$ and $\pi^{DD}$ are defined from the patient's optimal action, not by this display.
-- source:
--   Çakıcı and Mills, On the Role of Teletriage in Healthcare Demand Management, author accepted manuscript (M&SOM, accepted May 2020; SSRN 2849635), p. 11 (PDF 11), display of π^ED(b), π^DD(b)

import Mathlib
import Definitions.Def_Teletriage_OneShot_Model

namespace Teletriage.OneShot

/-- Display, p. 11: without teletriage, `π^ED(b) = 1` and `π^DD(b) = 0` for `b ≥ b0`, and
`π^ED(b) = π^DD(b) = b` for `b < b0`. -/
theorem pi_noTT (P : Params) (hS : P.Standing) (b : ℝ)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    piED P b = (if b0 P ≤ b then 1 else b) ∧ piDD P b = (if b0 P ≤ b then 0 else b) := by sorry

end Teletriage.OneShot
