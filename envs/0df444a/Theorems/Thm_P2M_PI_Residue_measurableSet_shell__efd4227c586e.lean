-- Prove2me | Theorems.Thm_P2M_PI_Residue_measurableSet_shell__efd4227c586e
-- name    : P2M_PI_Residue_measurableSet_shell__efd4227c586e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:35.683454+00:00
-- url     : https://prove2.me/theorems/842bd5b3-d6f1-5a6d-acc1-df414b223d75
-- title:
--   P2 M PI Residue measurable Set shell  efd4227c586e: P2 M PI Residue measurable Set shell  efd4227c586e
-- statement:
--   The P2 M PI Residue measurable Set shell  efd4227c586e construction uses the P2 M PI Residue measurable Set shell  efd4227c586e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L34-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]

theorem P2M_PI_Residue_measurableSet_shell__efd4227c586e : MeasurableSet (shell K) := by sorry

alias «PI».«Residue».«measurableSet_shell'» := P2M_PI_Residue_measurableSet_shell__efd4227c586e
