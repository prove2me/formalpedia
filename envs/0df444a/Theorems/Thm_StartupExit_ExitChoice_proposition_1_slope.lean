-- Prove2me | Theorems.Thm_StartupExit_ExitChoice_proposition_1_slope
-- name    : StartupExit.ExitChoice.proposition_1_slope
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:45.827757+00:00
-- url     : https://prove2.me/theorems/0aa49b89-fd74-4892-bc61-0384d6430c9f
-- title:
--   Proof of Proposition 1, Online Appendix A2 — for every cost c ∈ [0, R], Π^F − Π^L is strictly decreasing in θ on [0, 1]
-- statement:
--   Assume the standing assumptions. For every cost $c\in[0,R]$ of trying the early market, the advantage of flexibility over late commitment,
--
--   $$\theta\ \longmapsto\ \Pi^F(c,\theta)-\Pi^L(\theta),$$
--
--   is strictly decreasing on $[0,1]$.
--
--   This is the claim "$\partial\Pi^F/\partial\theta<\partial\Pi^L/\partial\theta$" of the proof of Proposition 1; it yields the single crossing that defines the threshold $\theta_H$ between flexibility and late commitment.
--
--   **Formalization Note** The page states a derivative inequality; it is formalized in its integrated form, strict decrease of $\Pi^F-\Pi^L$, which also holds across the point where $\underline v^*$ leaves $-1$ (where $\Pi^F$ need not be differentiable) and includes $c=R$, where $\Pi^F\equiv\Pi^E$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), Online Appendix A2 (PDF 36), proof of Proposition 1, "it can be shown as in the proof of Lemma A2.3 that ∂Π^F/∂θ < ∂Π^L/∂θ"

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_Model

namespace StartupExit.ExitChoice

theorem proposition_1_slope (P : Params) (hS : P.Standing) :
    ∀ c ∈ Set.Icc 0 P.R,
      StrictAntiOn (fun θ => PiF P c θ - PiL P θ) (Set.Icc 0 1) := by sorry

end StartupExit.ExitChoice
