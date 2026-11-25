-- Prove2me | Theorems.Thm_PI_FinKW_psiV_liftOne_ne
-- name    : PI.FinKW.psiV_liftOne_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:43.4478+00:00
-- url     : https://prove2.me/theorems/e2fa1197-e16f-40b9-920b-439916e5632c
-- title:
--   Fin KW: psi V lift One ne
-- statement:
--   The Fin KW construction uses the psi V lift One ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean#L50-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem PI.FinKW.psiV_liftOne_ne (I : AutInst) {v w : HeightOneSpectrum (𝓞 I.F)} (hw : w ≠ v)
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : psiV I w (liftOne I v y) = 0 := by sorry
