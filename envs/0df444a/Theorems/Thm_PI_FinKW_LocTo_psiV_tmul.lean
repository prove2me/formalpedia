-- Prove2me | Theorems.Thm_PI_FinKW_LocTo_psiV_tmul
-- name    : PI.FinKW.LocTo.psiV_tmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:27.552814+00:00
-- url     : https://prove2.me/theorems/58827966-e3f5-46e1-a599-b69322611b1c
-- title:
--   Loc To: psi V tmul
-- statement:
--   The Loc To construction uses the psi V tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L13-L17

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

theorem PI.FinKW.LocTo.psiV_tmul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) (a : Formalism.MainNotions.S.Af I.F) :
    psiV I v (e ⊗ₜ[I.F] a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v a ⊗ₜ[I.F] e := by sorry
