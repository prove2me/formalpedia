-- Prove2me | Theorems.Thm_PI_KerDetFinW_detOrdFin
-- name    : PI.KerDetFinW.detOrdFin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:33:33.05995+00:00
-- url     : https://prove2.me/theorems/c63dbb0c-55d5-442a-b3e4-acc4eebf11f7
-- title:
--   Ker Det Fin W: det Ord Fin
-- statement:
--   The Ker Det Fin W construction uses the det Ord Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsDenomBackward.lean#L77-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelFiniteness/ExistsDenomBackward.lean#L77-L91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso

theorem PI.KerDetFinW.detOrdFin : DetOrdFin := by sorry
