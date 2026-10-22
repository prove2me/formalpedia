-- Prove2me | Theorems.Thm_TBSGStrategyIteration_modValue_eq_sub
-- name    : TBSGStrategyIteration.modValue_eq_sub
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:45:52.958293+00:00
-- url     : https://prove2.me/theorems/a66a41af-9eb6-42bc-996b-965c3dcaaac5
-- title:
--   Lemma 3.6 — modified values are value differences
-- statement:
--   For every two strategy profiles $\pi', \pi$, the value vector of $\pi'$ under the modified costs $c^\pi$ equals the difference of the ordinary value vectors:
--   $$v^\pi_{\pi'} = v_{\pi'} - v_\pi .$$
--   The potential transformation $c \mapsto c^\pi$ thus shifts every value vector by $v_\pi$.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 5, Lemma 3.6

import Mathlib
import Definitions.Def_TBSGStrategyIteration_modCost

namespace TBSGStrategyIteration

/-- Lemma 3.6: for every two strategy profiles `π', π`, the value vector of `π'` under the
modified costs `c^π` is `v^π_{π'} = v_{π'} − v_π`. -/
theorem modValue_eq_sub {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π' π : Profile G) :
    modValue G π π' = value G π' - value G π := by sorry

end TBSGStrategyIteration
