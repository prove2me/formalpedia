-- Prove2me | Theorems.Thm_RespSourcing_Transparent_ds_vs_rn
-- name    : RespSourcing.Transparent.ds_vs_rn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:13.628985+00:00
-- url     : https://prove2.me/theorems/e4b7fa66-99f2-4646-9179-b8fea8cb9f57
-- title:
--   Appendix, Proposition 1 proof — dual versus responsible niche
-- statement:
--   Let $\Pi^{DS}$ and $\Pi^{RN}$ be the expected profits of dual and responsible niche sourcing. Under the standing parameter ranges,
--
--   $$\Pi^{DS}>\Pi^{RN}\iff \phi[c_{VP}+\alpha\theta(v+r-c_R)]<(1-\theta)(v-c_{NR}).$$
--
--   This is one of the two responsible-sourcing comparisons that delimit the dual-sourcing region.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2742, Appendix, proof of Proposition 1; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Appendix, proof of Proposition 1, p. 2742: DS versus RN. -/
theorem ds_vs_rn (p : Params) (hp : p.Standing) :
    (profit p .RN < profit p .DS ↔
      p.φ * (p.cVP + p.α * p.θ * (p.v + p.r - p.cR)) <
        (1 - p.θ) * (p.v - p.cNR)) := by sorry

end RespSourcing.Transparent
