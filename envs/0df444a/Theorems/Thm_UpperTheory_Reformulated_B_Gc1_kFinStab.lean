-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Gc1_kFinStab
-- name    : UpperTheory.Reformulated.B.Gc1.kFinStab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:10.467808+00:00
-- url     : https://prove2.me/theorems/29d7cfde-a029-4093-a44c-b00790159711
-- title:
--   Gc1: k Fin Stab
-- statement:
--   The Gc1 construction uses the k Fin Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/KsetSubset.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/KsetSubset.lean#L12-L22

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsInvariantSubspace
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KsetSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Gc1.kFinStab :
    CompanionTheory.D.DSIC.KFinStab := by sorry
