-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_lemma_2
-- name    : PrimalDualSubgrad.DA.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:31.766986+00:00
-- url     : https://prove2.me/theorems/62d2ad6f-0a8b-4fbf-91ae-e111230020fd
-- title:
--   Lemma 2 — ξ_D(s) ≤ βD + V_β(s)
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$. For every $s \in E^*$, $D \ge 0$ and $\beta > 0$,
--   $$\xi_D(s) \le \beta D + V_\beta(s). \qquad (2.7)$$
--
--   It compares the support function of the level set $F_D$ with the smoothed function $V_\beta$, and turns bounds on $V_\beta$ into bounds on the gap.
--
--   **Formalization Note** The page states the lemma for $\beta \ge 0$; $V_\beta$ is defined in (2.1) only for $\beta > 0$ (for $\beta = 0$ and unbounded $Q$ it is $+\infty$), so the statement is for $\beta > 0$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 8, Lemma 2, (2.7)

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting

namespace PrimalDualSubgrad.DA

/-- Lemma 2 (p. 8), (2.7): for `D ≥ 0`, `β > 0` and `s ∈ E*`, `ξ_D(s) ≤ βD + V_β(s)`.
(The page says `β ≥ 0`; `V_0` is not defined by (2.1) and is `+∞` on unbounded `Q`.) -/
theorem lemma_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (D β : ℝ) (hD : 0 ≤ D) (hβ : 0 < β) (s : StrongDual ℝ E) :
    xi P D s ≤ β * D + V P β s := by sorry

end PrimalDualSubgrad.DA
