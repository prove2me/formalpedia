-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma4_best_response_limits
-- name    : StrategicQR.Game.lemma4_best_response_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:46.579475+00:00
-- url     : https://prove2.me/theorems/3f72cc9c-741e-4194-9d36-feb0dc16e133
-- title:
--   Lemma 4 (ii), p. 15 — $\lim_{\hat q\to0}v^*(\hat q)=\bar v$ and $\lim_{\hat q\to\infty}v^*(\hat q)=\underline v$
-- statement:
--   Let $0<\alpha\le1$. The consumer best-response correspondence $v^*(\hat q)$ satisfies:
--
--   1. $\lim_{\hat q\to0^+}v^*(\hat q)=\bar v$: for every $\varepsilon>0$ there is $\delta>0$ such that for every $\hat q\in(0,\delta)$ every best response $v$ to $\hat q$ satisfies $|v-\bar v|<\varepsilon$;
--   2. if $\theta>0$, $\lim_{\hat q\to\infty}v^*(\hat q)=\underline v$: for every $\varepsilon>0$ there is $Q$ such that for every $\hat q\ge Q$ every best response $v$ to $\hat q$ satisfies $|v-\underline v|<\varepsilon$.
--
--   A tiny expected inventory makes every strategic consumer buy at the full price; a huge one makes them all wait. These limits are what the existence proof of Theorem 1 uses.
--
--   **Formalization Note** $v^*(\hat q)$ is a correspondence (p. 11), so each limit is stated for all best responses at once. The second limit needs $\theta>0$: at $\theta=0$ strategic consumers are never served in the sale period (p. 15), every best response is $\bar v$, and the limit is $\bar v$, not $\underline v$. The appendix uses $v_M-p<\underline v-v_B$ "by assumption"; the standing assumption $v_M-p\le\underline v-v_B$ suffices for the statement as given.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 15, Lemma 4 (ii); Technical Appendix p. 4 (PDF 36), proof of Lemma 4

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

open Filter Topology

/-- Lemma 4 (ii) (p. 15; proof on Technical Appendix p. 4), for the best-response
correspondence `v*(q̂)`: every best response to a small enough belief `q̂ > 0` is within `ε` of
`v̄` (`lim_{q̂→0} v*(q̂) = v̄`), and, when `θ > 0`, every best response to a large enough `q̂` is
within `ε` of `v̲` (`lim_{q̂→∞} v*(q̂) = v̲`). -/
theorem lemma4_best_response_limits (M : Model) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∀ ε > 0, ∀ᶠ q in 𝓝[>] (0 : ℝ), ∀ v, IsConsumerBR M α q v → |v - M.vhi| < ε) ∧
    (0 < M.θ → ∀ ε > 0, ∀ᶠ q in atTop, ∀ v, IsConsumerBR M α q v → |v - M.vlo| < ε) := by sorry

end StrategicQR.Game
