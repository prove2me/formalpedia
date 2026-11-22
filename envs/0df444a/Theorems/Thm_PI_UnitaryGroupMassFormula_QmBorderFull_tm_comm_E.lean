-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_tm_comm_E
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.tm_comm_E
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:35.819172+00:00
-- url     : https://prove2.me/theorems/49a76b73-26d4-4690-b427-3dfffd99b46c
-- title:
--   Qm Border Full: tm comm E
-- statement:
--   The Qm Border Full construction uses the tm comm E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean#L48-L52

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

theorem PI.UnitaryGroupMassFormula.QmBorderFull.tm_comm_E {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (u : ℂ) (e c d : Fin n) (h1 : e ≠ c) (h2 : d ≠ e) : Tm E u e e * E c d = E c d * Tm E u e e := by sorry
