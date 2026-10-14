-- Prove2me | Theorems.Thm_PlatformEntry_Regimes_prop2_num_factorization
-- name    : PlatformEntry.Regimes.prop2_num_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:50.502217+00:00
-- url     : https://prove2.me/theorems/8ac36eba-1cab-49fb-85ff-f31ac38d7726
-- title:
--   Proof of Proposition 2, PDF p. 35 — Num(f,β,δ) = 4N₅² − D² factors as (11) times a second factor
-- statement:
--   For all real $\delta, f, \beta$,
--
--   $$
--   \begin{aligned}
--   &4\big(4(1+\delta) - 2\beta(2-\delta+\delta^2) + \beta^3(1+f) - \beta^2(2+f+\delta f)\big)^2 \\
--   &\quad - \big(8 - 8\delta^2 f + 8\beta\delta(1+f) - 2\beta^3\delta f(1+f) + \beta^4(1+f)^2 + 2\beta^2(-4-3f+\delta^2(-1+f^2))\big)^2 \\
--   &= \big(-\beta^4(1+f)^2 + 8\delta(1+\delta f) + 2\beta^3(1+f)(1+\delta f) - 4\beta(2+\delta+\delta^2+2\delta f) + \beta^2(-2\delta f + 4(1+f) - 2\delta^2(-1+f^2))\big) \\
--   &\quad \times \big(\beta^4(1+f)^2 - 2\beta^3(1+f)(-1+\delta f) + 8(2+\delta-\delta^2 f) - 4\beta(2+\delta^2-\delta(3+2f)) + 2\beta^2(-6-4f-\delta f+\delta^2(-1+f^2))\big).
--   \end{aligned}
--   $$
--
--   The left side is $\mathrm{Num}(f,\beta,\delta)$, the numerator of $H - 1/4$ over $4D^2$; the first factor on the right is the function (11) of Lemma 3. The identity turns the condition $H > 1/4$ into a sign condition on (11).
-- source:
--   Qi, Song & Xiao, Coopetition in Platform-Based Retailing: On the Platform’s Entry, authors' manuscript with Online Supplement (2024-08-03; Management Science DOI 10.1287/mnsc.2023.00260), Online Supplement, Appendix A, proof of Proposition 2, PDF p. 35

import Mathlib
import Definitions.Def_PlatformEntry_Regimes_Model

namespace PlatformEntry.Regimes

theorem prop2_num_factorization (δ f β : ℝ) :
    4 * N5 δ f β ^ 2 - D δ f β ^ 2 = P11 δ f β * S2 δ f β := by sorry

end PlatformEntry.Regimes
