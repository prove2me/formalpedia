-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_SeriesSubgroup_XTShape_holds
-- name    : UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:07.184864+00:00
-- url     : https://prove2.me/theorems/c879b759-d558-4da0-af4f-95ef3fe4d30b
-- title:
--   Series Subgroup: XTShape holds
-- statement:
--   The Series Subgroup construction uses the XTShape holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SeriesSubgroup.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SeriesSubgroup.lean#L114-L117

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvOfUnitCoeffMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FormalGroupCoeffMem
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.SeriesSubgroup

theorem UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds : Formalism.L2.Th1.E.XTShape := by sorry
