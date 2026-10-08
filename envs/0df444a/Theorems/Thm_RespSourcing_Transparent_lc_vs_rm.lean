-- Prove2me | Theorems.Thm_RespSourcing_Transparent_lc_vs_rm
-- name    : RespSourcing.Transparent.lc_vs_rm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:24.025632+00:00
-- url     : https://prove2.me/theorems/fab37d56-530a-4621-bbc7-f1d48f99e701
-- title:
--   Appendix, Proposition 1 proof — low-cost versus responsible mass market
-- statement:
--   Let $\Pi^{LC}$ and $\Pi^{RM}$ be the expected profits of low-cost and responsible mass market sourcing, and set $\Delta=c_R-c_{NR}$. Under the standing parameter ranges,
--
--   $$\Pi^{LC}>\Pi^{RM}\iff \phi[\alpha\theta(v-c_{NR})+c_{VP}]<\Delta.$$
--
--   This is the paper's direct-cost and lost-demand comparison between using only the risky supplier and using only the responsible supplier.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2742, Appendix, proof of Proposition 1; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Appendix, proof of Proposition 1, p. 2742: LC versus RM. -/
theorem lc_vs_rm (p : Params) (hp : p.Standing) :
    (profit p .RM < profit p .LC ↔
      p.φ * (p.α * p.θ * (p.v - p.cNR) + p.cVP) < p.Δ) := by sorry

end RespSourcing.Transparent
