-- Prove2me | Theorems.Thm_PI_FinKW_LocTo_psiV_inclE
-- name    : PI.FinKW.LocTo.psiV_inclE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:30:40.620801+00:00
-- url     : https://prove2.me/theorems/7f27ca4b-59be-4b54-ade0-22a81b602efa
-- title:
--   Loc To: psi V incl E
-- statement:
--   The Loc To construction uses the psi V incl E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L19-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinKW PI.FinKW.LocTo
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem PI.FinKW.LocTo.psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    psiV I v (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) e) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) e := by sorry
