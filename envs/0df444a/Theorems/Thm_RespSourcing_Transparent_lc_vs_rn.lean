-- Prove2me | Theorems.Thm_RespSourcing_Transparent_lc_vs_rn
-- name    : RespSourcing.Transparent.lc_vs_rn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:21.008758+00:00
-- url     : https://prove2.me/theorems/d0b1d950-029c-46e9-bee7-35fb9f9e396d
-- title:
--   Appendix, Proposition 1 proof — low-cost versus responsible niche
-- statement:
--   Let $\Pi^{LC}$ and $\Pi^{RN}$ be the expected profits of low-cost and responsible niche sourcing. Under the standing parameter ranges,
--
--   $$\Pi^{LC}>\Pi^{RN}\iff \phi[\alpha\theta(v-c_{NR})+c_{VP}]<(v-c_{NR})-\theta(v+r-c_R).$$
--
--   This comparison supplies the responsible-niche competitor condition for the low-cost region of Proposition 1.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2742, Appendix, proof of Proposition 1; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Appendix, proof of Proposition 1, p. 2742: LC versus RN. -/
theorem lc_vs_rn (p : Params) (hp : p.Standing) :
    (profit p .RN < profit p .LC ↔
      p.φ * (p.α * p.θ * (p.v - p.cNR) + p.cVP) <
        (p.v - p.cNR) - p.θ * (p.v + p.r - p.cR)) := by sorry

end RespSourcing.Transparent
