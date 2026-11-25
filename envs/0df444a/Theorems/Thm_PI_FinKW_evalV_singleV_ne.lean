-- Prove2me | Theorems.Thm_PI_FinKW_evalV_singleV_ne
-- name    : PI.FinKW.evalV_singleV_ne
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:43.905638+00:00
-- url     : https://prove2.me/theorems/1a7c4954-edd1-40f1-ac04-6eea1979ee09
-- title:
--   Fin KW: eval V single V ne
-- statement:
--   The Fin KW construction uses the eval V single V ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean#L30-L36

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
open Classical

theorem PI.FinKW.evalV_singleV_ne (I : AutInst) {v w : HeightOneSpectrum (𝓞 I.F)} (hw : w ≠ v)
    (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV I.F v c) = 0 := by sorry
