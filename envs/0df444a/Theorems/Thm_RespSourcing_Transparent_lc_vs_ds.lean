-- Prove2me | Theorems.Thm_RespSourcing_Transparent_lc_vs_ds
-- name    : RespSourcing.Transparent.lc_vs_ds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:21.436032+00:00
-- url     : https://prove2.me/theorems/da0a8528-2e7a-4a39-aea5-a35990e21bd0
-- title:
--   Appendix, Proposition 1 proof — low-cost versus dual sourcing
-- statement:
--   Let $\Pi^{LC}$ and $\Pi^{DS}$ be the expected profits of low-cost and dual sourcing, and let $\Delta=c_R-c_{NR}$. Under the model's standing ranges, if $\theta>0$ and $\alpha\phi<1$, then
--
--   $$\Pi^{LC}>\Pi^{DS}\iff r<\Delta,\qquad \Pi^{DS}>\Pi^{LC}\iff r>\Delta.$$
--
--   These comparisons identify which of the two strategies can be preferred on either side of the cost premium.
--
--   **Formalization Note** The strict equivalences need $\theta>0$ and $\alpha\phi<1$: at either degenerate boundary the two profits can tie even when $r\ne\Delta$.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), p. 2742, Appendix, proof of Proposition 1; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

namespace RespSourcing.Transparent

/-- Appendix, proof of Proposition 1, p. 2742: the two strict LC/DS comparisons. -/
theorem lc_vs_ds (p : Params) (hp : p.Standing)
    (hθ : 0 < p.θ) (hαφ : p.α * p.φ < 1) :
    (profit p .DS < profit p .LC ↔ p.r < p.Δ) ∧
    (profit p .LC < profit p .DS ↔ p.Δ < p.r) := by sorry

end RespSourcing.Transparent
