-- Prove2me | Theorems.Thm_ShockWear_Inherit_hazard_bound25
-- name    : ShockWear.Inherit.hazard_bound25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:00.223026+00:00
-- url     : https://prove2.me/theorems/32ed724c-a740-43fe-b6f5-fcbebde2daa1
-- title:
--   Equation (2.5) — the shock-model hazard is at most the shock rate
-- statement:
--   For a Poisson shock model with rate $\lambda>0$ and survival probabilities $1\geq\bar P_0\geq\bar P_1\geq\cdots\geq0$, let $\bar H$ be (2.1) and $h$ its positive-time density (2.3). Then, for every $t>0$,
--
--   $$h(t)\leq\lambda\bar H(t).$$
--
--   Wherever $\bar H(t)>0$, this is the paper's bound $r(t)=h(t)/\bar H(t)\leq\lambda$. It supplies the boundary estimate used in the proof of Theorem 3.1(3.2).
--
--   **Formalization Note** The inequality is cross-multiplied so it remains meaningful when survival is zero; no totalized real division is used.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 629, (2.4)–(2.5); https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model

namespace ShockWear.Inherit

/-- Equation (2.5), expressed without dividing by a possibly zero survival value. -/
theorem hazard_bound25 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 < t → shockDens lam P t ≤ lam * ShockWear.CumDamage.shockSurv lam P t := by sorry

end ShockWear.Inherit
