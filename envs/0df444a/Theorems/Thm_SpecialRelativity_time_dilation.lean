-- Prove2me | Theorems.Thm_SpecialRelativity_time_dilation
-- name    : SpecialRelativity.time_dilation
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T01:49:19.142895+00:00
-- url     : https://prove2.me/theorems/01deba3f-2569-55b9-9a1d-b6d57a503757
-- title:
--   Time dilation: proper time along an inertial worldline
-- statement:
--   **Time dilation — proper time along an inertial worldline.**
--
--   Let a clock move inertially with velocity `v` in coordinate-time parametrization ($v_0 = 1$, spatial speed $s < 1$), so its worldline is $\gamma(t) = a + t\,v$ for some fixed event `a`, and let $t_1, t_2$ be parameter values with $t_1 \le t_2$ in effect (the integral is over $t_1 \,.\,.\, t_2$).
--
--   **Conclusion:** the proper time elapsed on the clock is
--
--   $$\Delta\tau \;=\; \sqrt{1 - s^2}\,\cdot\,(t_2 - t_1),$$
--
--   where $s = $ `spatialSpeed v`. Since $0 \le s < 1$, the factor $\sqrt{1 - s^2} \le 1$, with equality only for the stationary clock: moving clocks run slower, with slowdown factor $1/\gamma = \sqrt{1 - s^2}$ — the content of the source's $\Delta t' = \gamma\,\Delta t$.
--
--   **Formalization note.** Along an affine worldline the velocity $\gamma'(t) = v$ is constant, so $\eta(\gamma', \gamma') = -v_0^2 + s^2 = -(1 - s^2)$ is constant and the integrand of `properTime` is the constant $\sqrt{1 - s^2}$; the assertion reduces to the integral of a constant (with `hv0 : v 0 = 1` supplying $v_0^2 = 1$ and `hsp` supplying reality of the square root). No hypothesis of small velocity: exact for all subluminal speeds.
-- source:
--   Wikipedia, Special relativity, https://en.wikipedia.org/wiki/Special_relativity (source of the quoted statements, reproduced verbatim in the definition file) (Time dilation: 'Moving clocks run slower'; the Lorentz factor gamma = 1/sqrt(1 - v2/c2))

import Mathlib
import Definitions.Def_SpecialRelativity

namespace SpecialRelativity

/-- Milestone: time dilation.  A clock moving inertially with velocity `v`
(`v 0 = 1` in coordinate-time parametrization, spatial speed `s < 1`) records,
between parameter values `t₁` and `t₂`, the proper time

`Δτ = √(1 - s²) · (t₂ - t₁)`,

strictly less than the coordinate time `t₂ - t₁` whenever the clock moves —
"Moving clocks run slower", with the slowdown factor `1/γ = √(1 - s²)` of the
source's `Δt' = γ Δt`. -/
theorem time_dilation (a v : Sp) (hv0 : v 0 = 1) (hsp : spatialSpeed v < 1) (t₁ t₂ : ℝ) :
    properTime (fun t => a + t • v) t₁ t₂
      = Real.sqrt (1 - spatialSpeed v ^ 2) * (t₂ - t₁) := by
  sorry

end SpecialRelativity
