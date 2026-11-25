-- Prove2me | Theorems.Thm_PI_GalTorsConj_W_OriginCoordinatesAdd_chord_alg
-- name    : PI.GalTorsConj.W.OriginCoordinatesAdd.chord_alg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:52.322994+00:00
-- url     : https://prove2.me/theorems/f65f9c19-6304-4873-95da-db9c5e47ca5c
-- title:
--   Origin Coordinates Add: chord alg
-- statement:
--   The Origin Coordinates Add construction uses the chord alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/AddLaw.lean#L73-L79

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

theorem PI.GalTorsConj.W.OriginCoordinatesAdd.chord_alg (x y x₂ y₂ g g' : ℂ) (hd : x - x₂ ≠ 0)
    (hy : y ^ 2 = 4 * x ^ 3 - g * x - g') (hy₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g * x₂ - g') :
    x - ((6 * x ^ 2 - g / 2) * (x - x₂) - (y - y₂) * y) / (x - x₂) ^ 2 / 2
      = addX x y x₂ y₂ := by sorry
