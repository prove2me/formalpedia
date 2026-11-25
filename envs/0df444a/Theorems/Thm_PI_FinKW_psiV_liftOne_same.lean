-- Prove2me | Theorems.Thm_PI_FinKW_psiV_liftOne_same
-- name    : PI.FinKW.psiV_liftOne_same
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:53.681382+00:00
-- url     : https://prove2.me/theorems/cb050872-73ab-4e94-9f55-64a8dc32a01a
-- title:
--   Fin KW: psi V lift One same
-- statement:
--   The Fin KW construction uses the psi V lift One same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/LocLift.lean#L38-L48

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

theorem PI.FinKW.psiV_liftOne_same (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) : psiV I v (liftOne I v y) = y := by sorry
