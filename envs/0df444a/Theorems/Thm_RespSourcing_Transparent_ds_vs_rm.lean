-- Prove2me | Theorems.Thm_RespSourcing_Transparent_ds_vs_rm
-- name    : RespSourcing.Transparent.ds_vs_rm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:18.728582+00:00
-- url     : https://prove2.me/theorems/bca5b17f-9890-4f7a-a5d2-f3c15e81c1fd
-- title:
--   Appendix, Proposition 1 proof — dual versus responsible mass market
-- statement:
--   Let $\Pi^{DS}$ and $\Pi^{RM}$ be the expected profits of dual and responsible mass market sourcing. Under the standing parameter ranges and with $\Delta=c_R-c_{NR}$,
--
--   $$\Pi^{DS}>\Pi^{RM}\iff \phi[c_{VP}+\alpha\theta(v+r-c_R)]<\theta r+(1-\theta)\Delta.$$
--
--   This is the second responsible-sourcing comparison that delimits the dual-sourcing region.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2742, Appendix, proof of Proposition 1; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Appendix, proof of Proposition 1, p. 2742: DS versus RM. -/
theorem ds_vs_rm (p : Params) (hp : p.Standing) :
    (profit p .RM < profit p .DS ↔
      p.φ * (p.cVP + p.α * p.θ * (p.v + p.r - p.cR)) <
        p.θ * p.r + (1 - p.θ) * p.Δ) := by sorry

end RespSourcing.Transparent
