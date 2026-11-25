-- Prove2me | Theorems.Thm_PI_DegenerateSiegelWeil_Scale_linIndep_mulTup
-- name    : PI.DegenerateSiegelWeil.Scale.linIndep_mulTup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:16:13.576804+00:00
-- url     : https://prove2.me/theorems/71932483-600f-51ce-b062-8113a9600d77
-- title:
--   Scale: lin Indep mul Tup
-- statement:
--   The Scale construction uses the lin Indep mul Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SiegelWeilVolume/MulTupApplyEqSum.lean#L40-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix
variable {K : Type} [CommRing K] {n M : ℕ}

theorem PI.DegenerateSiegelWeil.Scale.linIndep_mulTup (D : (Matrix (Fin n) (Fin n) K)ˣ) {X : Fin n → Fin M → K}
    (hX : LinearIndependent K X) : LinearIndependent K (mulTup (D : Matrix (Fin n) (Fin n) K) X) := by sorry
