-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_JumpSetsAlt_hostReal_of
-- name    : UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:44:59.906974+00:00
-- url     : https://prove2.me/theorems/066f85c6-619a-4662-a91e-e297f2e022a5
-- title:
--   Jump Sets Alt: host Real of
-- statement:
--   The Jump Sets Alt construction uses the host Real of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean#L205-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean#L205-L318

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical

theorem UpperTheory.Reformulated.B.JumpSetsAlt.hostReal_of :
    UpperTheory.Reformulated.B.JumpSetsAlt.HostGalois → UpperTheory.Reformulated.B.JumpSetsAlt.HostGalSpec → UpperTheory.Reformulated.B.JumpSetsAlt.HostConj → UpperTheory.Reformulated.B.JumpSetsAlt.HostReal := by sorry
