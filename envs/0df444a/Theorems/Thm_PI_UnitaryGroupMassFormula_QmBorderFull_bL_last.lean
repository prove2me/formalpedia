-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bL_last
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.bL_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:45:53.466971+00:00
-- url     : https://prove2.me/theorems/b267aeec-6b54-49bb-8fd2-b374a823b231
-- title:
--   Qm Border Full: b L last
-- statement:
--   The Qm Border Full construction uses the b L last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean#L54-L63

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderFull
import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.bL_last {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) :
    bE e (bS v es) ∘ (Fin.last (m + 1)).succAbove = bE e v := by sorry
