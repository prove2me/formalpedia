-- Prove2me | Theorems.Thm_VerticalOwnership_CheapTalk_eq_E_2
-- name    : VerticalOwnership.CheapTalk.eq_E_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:36.19061+00:00
-- url     : https://prove2.me/theorems/56f04e57-1cd5-4984-bf73-70b9ddd78e33
-- title:
--   (E.2), p. 46 — β̳ = z_r/(1 − z_r) · ((1 − z_s)/(R(Δ) − z_s) − 1)
-- statement:
--   In the model of the mission, with $\Delta=\mu_H-\mu_L$ and $R(\Delta)=\frac1\Delta\int_{F^{-1}(z_s)}^{\Delta+F^{-1}(z_s)}F(x)\,dx$, the cheap-talk threshold (defined as a ratio of expected-profit differences) has the closed form
--   $$\underline{\underline{\beta}}=\frac{z_r}{1-z_r}\left(\frac{1-z_s}{R(\Delta)-z_s}-1\right).$$
--
--   The closed form shows that the threshold depends on the demand distribution and the information gap only through the average $R(\Delta)$ of $F$ over $[F^{-1}(z_s),\,F^{-1}(z_s)+\Delta]$.
--
--   **Formalization Note** The denominator $R(\Delta)-z_s$ is nonzero under the standing assumptions; no hypothesis to that effect is added.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 46, Appendix E, Proof of Theorem 2, (E.2); also (14), p. 13

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace VerticalOwnership.CheapTalk

theorem eq_E_2 (M : Model) (hM : M.Standing) :
    M.betaCT = M.zr / (1 - M.zr) * ((1 - M.zs) / (M.R M.Δ - M.zs) - 1) := by sorry

end VerticalOwnership.CheapTalk
