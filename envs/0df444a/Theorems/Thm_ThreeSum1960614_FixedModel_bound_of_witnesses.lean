-- Prove2me | Theorems.Thm_ThreeSum1960614_FixedModel_bound_of_witnesses
-- name    : ThreeSum1960614.FixedModel.bound_of_witnesses
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T13:34:10.365235+00:00
-- url     : https://prove2.me/theorems/6600f18a-f5d3-4c32-9b82-95b2f500c864
-- title:
--   Four-charge elimination for the expansion-232 analytic model
-- statement:
--   Let $e>0$ be the block fraction, $b$ the band exponent, $S$ the saving, $t$ the switch point, $\tau$ the terminal threshold, $\rho$ the ratio parameter, and $R$ a common upper bound on the model charges. Assume the published predicate $\operatorname{ModelFeasible}(232,e,b,S,t,\tau,\rho,R)$.
--
--   Let $E_0,\kappa_0,\rho_0,s,G,H$ be the exact rational witnesses in the shared definitions. Suppose $E_0\le E(232)$, $\kappa_0\le\kappa(232)$, $\rho_0\le\rho$, and that the two sides of the switch obey
--   $$t\le s\Longrightarrow\gamma(232,t)\le G,\qquad s\le t\Longrightarrow H\le h(t),$$
--   where $h$ is binary entropy in base two. Then
--   $$R>1.96061349120.$$
--   Only the fixed analytic model is bounded; this is not a lower bound for arbitrary 3SUM algorithms.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/FixedModelAlgebra.lean#L22-L95

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_FixedModelAlgebra
import Definitions.Def_ThreeSum1960614_ModelWitnessPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

open ThreeSum1960614 ThreeSum1960614.FixedModel

theorem ThreeSum1960614.FixedModel.bound_of_witnesses (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R)
    (hE : e0 ≤ E 232) (hk : k0 ≤ kappa 232) (hrho : ratio0 ≤ ratio)
    (hgamma : th ≤ split → gamma 232 th ≤ gammaCap)
    (hentropy : split ≤ th → entropyFloor ≤ entropy th) : lowerTarget < R := by sorry
