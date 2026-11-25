-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_PoincareLelongAlt_of_found_e6d09a0ad8bf
-- name    : P2M_GroundTheory_Heights__Heights_Targets_PoincareLelongAlt_of_found_e6d09a0ad8bf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:39:36.969039+00:00
-- url     : https://prove2.me/theorems/cfcf22a3-3824-5238-85b1-ad446a7e0850
-- title:
--   P2 M Ground Theory Heights  Heights Targets Poincare Lelong Alt of found e6d09a0ad8bf: P2 M Ground Theory Heights  Heights Targets Poincare Lelong Alt of found e6d09a0ad8bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Poincare Lelong Alt of found e6d09a0ad8bf construction uses the P2 M Ground Theory Heights  Heights Targets Poincare Lelong Alt of found e6d09a0ad8bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PoincareLelongAlt.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PoincareLelongAlt.lean#L11-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongRegularised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PoincareLelongAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem P2M_GroundTheory_Heights__Heights_Targets_PoincareLelongAlt_of_found_e6d09a0ad8bf (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«PoincareLelongAlt».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_PoincareLelongAlt_of_found_e6d09a0ad8bf
