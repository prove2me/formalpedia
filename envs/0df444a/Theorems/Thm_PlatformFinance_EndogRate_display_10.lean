-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_display_10
-- name    : PlatformFinance.EndogRate.display_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:44.433528+00:00
-- url     : https://prove2.me/theorems/5579e760-91c5-4952-a689-8ae6076e7d05
-- title:
--   (10), p. 35/41 — the platform's equilibrium profit under platform financing when δ ≤ δr
-- statement:
--   Under the standing assumptions ($0<\delta<a$, $0\le\varphi<1$, $c>0$, $r_f\ge0$, $(1-\varphi)a>c(1+r_f)$) and $r>-1$, $c(1+r)<(a+\delta)(1-\varphi)$, suppose $\delta \le \delta_r = \frac{a(1-\varphi)-c(1+r)}{(2+\sqrt6)(1-\varphi)}$. Then in every subgame-perfect equilibrium $(w, q(\cdot))$ of the platform-financing game at rate $r$, the platform's profit $\Pi^P_p = \mathbb E[\varphi(\tilde a-q)q + \min\{(1-\varphi)(\tilde a-q)q,\, wq(1+r)\}] - wq(1+r_f)$, evaluated at $q=q(w)$, equals
--
--   $$\Pi^P_p(r) = \frac{(a(1-\varphi)-c(1+r))\big(a(1-\varphi)(r(\varphi+2)-2r_f(1-\varphi)+3\varphi) - c(r+1)(r(\varphi-2)+2r_f(1-\varphi)-\varphi)\big)}{16(r+1)(1-\varphi)^2}.$$
--
--   This is display (10) of the paper; it reduces the platform's rate-setting problem of §5 to a one-variable rational function when uncertainty is small.
--
--   **Formalization Note** The page lists this formula in the proof of Proposition 2 (p. 35) under the heading "the equilibrium profits under trade credit", a slip for platform financing; it is labelled (10) on p. 41 and restated on p. 43. The hypothesis $c(1+r)<(a+\delta)(1-\varphi)$ follows from $\delta \le \delta_r$ and is kept as the page's condition (ii).
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 35 (proof of Proposition 2, Π^P_p for δ ≤ δr), p. 41 display (10), p. 43

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Display (10) (pp. 35, 41, 43): when `δ ≤ δr`, the platform's equilibrium profit under
platform financing equals the closed form `PiP0`. -/
theorem display_10 (a δ φ c rf r : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ)) (hδr : δ ≤ deltaR a φ c r)
    (σ : Profile) (hσ : IsSPEP a δ φ c rf r σ) :
    platformProfitP a δ φ rf r σ = PiP0 a φ c rf r := by sorry

end PlatformFinance.EndogRate
