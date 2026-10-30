-- Prove2me | Theorems.Thm_ProjectOutsourcing_SingleTask_disc_eq_integral_cdf
-- name    : ProjectOutsourcing.SingleTask.disc_eq_integral_cdf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:01.743913+00:00
-- url     : https://prove2.me/theorems/f88e4c87-06ae-4707-8207-80d029fac167
-- title:
--   §3, p. 7 — the expected discount factor by integration by parts: E_Z[e^{−sZ/r}] = s ∫₀^∞ e^{−st} F(rt) dt (stated for any rate s > 0)
-- statement:
--   Let $Z\ge 0$ have cdf $F$ and let the work rate be $r>0$, so that the task duration $T=Z/r$ has cdf $t\mapsto F(rt)$. For every discount rate $s>0$,
--   $$\mathbb E_Z\big[e^{-sZ/r}\big]=s\int_0^\infty e^{-st}F(rt)\,dt .$$
--
--   With $s=\alpha$ this is the identity $\mathbb E_Z[e^{-\alpha T}]=\alpha\int_0^\infty e^{-\alpha t}F(rt)\,dt$ of p. 7. It expresses the expected discount factor through the cdf and is how Assumption 1 (concavity of $F$) turns into concavity in $r$ of the discounted reward.
--
--   **Formalization Note** The page states the identity for the discount rate $\alpha$. It is stated here for an arbitrary rate $s>0$, which also covers the rate $\alpha+\beta$ of the time-based contract; the page's case is $s=\alpha$. The intermediate Stieltjes form $\int_0^\infty e^{-\alpha t}\,d(F(rt))$ is not stated separately. The model's standing assumptions are hypotheses.
-- source:
--   Hou, Lu, Deng, Shen, Coordinating Project Outsourcing through Bilateral Contract Negotiations, author manuscript (SSRN 3443865; MSOM, doi:10.1287/msom.2020.0911), p. 7, §3, expected discount rate E_Z[e^{−αT}] (integration by parts)

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

namespace ProjectOutsourcing.SingleTask

theorem disc_eq_integral_cdf (M : Model) (hM : M.Valid) (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    disc M s r = s * ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * M.F (r * t) := by sorry

end ProjectOutsourcing.SingleTask
