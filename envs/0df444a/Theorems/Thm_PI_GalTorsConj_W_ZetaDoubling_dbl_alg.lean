-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_ZetaDoubling_dbl_alg
-- name    : PI.GalTorsConj.W.ZetaDoubling.dbl_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:20.313795+00:00
-- url     : https://prove2.me/theorems/5159b0a7-87d0-4da4-886a-9b4f670db1f4
-- title:
--   Zeta Doubling: dbl alg
-- statement:
--   The Zeta Doubling construction uses the dbl alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddDbl.lean#L90-L94

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

theorem PI.GalTorsConj.W.ZetaDoubling.dbl_alg (x y g : ℂ) (hy : y ≠ 0) :
    x - (12 * x * y * y - (6 * x ^ 2 - g / 2) * (6 * x ^ 2 - g / 2)) / y ^ 2 / 4 = dblX x y g := by sorry
