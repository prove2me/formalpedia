-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_hasDerivAt_wp
-- name    : PI.GalTorsConj.W.OriginCoordinatesAdd.hasDerivAt_wp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:15.095952+00:00
-- url     : https://prove2.me/theorems/d8bf186a-cf66-4850-903b-d56ea3fc64c9
-- title:
--   Origin Coordinates Add: has Deriv At wp
-- statement:
--   The Origin Coordinates Add construction uses the has Deriv At wp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L14-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Formalism.L2.Th1.F
open Filter Topology
open PI.GalTorsConj.W.OriginCoordinatesAdd

theorem PI.GalTorsConj.W.OriginCoordinatesAdd.hasDerivAt_wp (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by sorry
