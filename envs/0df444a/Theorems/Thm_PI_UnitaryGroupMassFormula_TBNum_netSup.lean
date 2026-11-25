-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TBNum_netSup
-- name    : PI.UnitaryGroupMassFormula.TBNum.netSup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:46.662949+00:00
-- url     : https://prove2.me/theorems/b8419995-9b3e-4b14-ba17-e8408cf2fc74
-- title:
--   TBNum: net Sup
-- statement:
--   The TBNum construction uses the net Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/SchwarzBallNumerics/NetSup.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/SchwarzBallNumerics/NetSup.lean#L8-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ScaledBoundInequalityHypothesesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_SchwarzBallNumerics_NetSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBNum
open ComplexConjugate

theorem PI.UnitaryGroupMassFormula.TBNum.netSup : ReciprocityTheory.ChartRestriction.G.TB.NetSupSt := by sorry
