-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_hasDerivAt_two_mul
-- name    : PI.GalTorsConj.W.ZetaDoubling.hasDerivAt_two_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:22.22219+00:00
-- url     : https://prove2.me/theorems/4ab5dfc0-eaef-49e5-9933-2d1be57996d9
-- title:
--   Zeta Doubling: has Deriv At two mul
-- statement:
--   The Zeta Doubling construction uses the has Deriv At two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L20-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
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
open PI.GalTorsConj.W.ZetaDoubling
open OriginCoordinatesAdd

theorem PI.GalTorsConj.W.ZetaDoubling.hasDerivAt_two_mul (z : ℂ) : HasDerivAt (fun y : ℂ => 2 * y) 2 z := by sorry
