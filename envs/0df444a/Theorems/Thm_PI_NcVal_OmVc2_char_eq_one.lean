-- Prove2me | Theorems.Thm_PI_NcVal_OmVc2_char_eq_one
-- name    : PI.NcVal.OmVc2.char_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:02.268358+00:00
-- url     : https://prove2.me/theorems/cd941188-dee7-5c40-a04b-3abed3fef8f4
-- title:
--   Om Vc2: char eq one
-- statement:
--   The Om Vc2 construction uses the char eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean#L11-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/MulTupDiagonal.lean#L11-L39

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

theorem PI.NcVal.OmVc2.char_eq_one {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (e p : G ≃ₜ+ G) (hp : ∀ x, p (p x) = x) (he : ∀ x, p (e (p x)) = e.symm x) :
    addEquivAddHaarChar e = 1 := by sorry
