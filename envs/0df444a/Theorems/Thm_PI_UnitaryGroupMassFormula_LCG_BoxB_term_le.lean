-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_term_le
-- name    : PI.UnitaryGroupMassFormula.LCG.BoxB.term_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:49:36.437978+00:00
-- url     : https://prove2.me/theorems/6462f3a4-ce9e-5d7c-99de-fa1e46c5e0b5
-- title:
--   Box B: term le
-- statement:
--   The Box B construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBound.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/BoxBound.lean#L44-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.BoxB
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace

theorem PI.UnitaryGroupMassFormula.LCG.BoxB.term_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ Real.sqrt n * (‖X‖ ^ k / k.factorial) := by sorry
