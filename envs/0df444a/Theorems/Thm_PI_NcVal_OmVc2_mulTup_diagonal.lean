-- Prove2me | Theorems.Thm_PI_NcVal_OmVc2_mulTup_diagonal
-- name    : PI.NcVal.OmVc2.mulTup_diagonal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:01.662279+00:00
-- url     : https://prove2.me/theorems/c8543e01-b902-5f76-9b5b-9c06c018b428
-- title:
--   Om Vc2: mul Tup diagonal
-- statement:
--   The Om Vc2 construction uses the mul Tup diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean#L59-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc2
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct
variable {K : Type} [CommRing K] {a M : ℕ}

theorem PI.NcVal.OmVc2.mulTup_diagonal (f : Fin a → K) (X : Fin a → Fin M → K) :
    mulTup (Matrix.diagonal f) X = fun j i => f j * X j i := by sorry
