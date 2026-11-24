-- Prove2me | Theorems.Thm_PI_FinKW_LocTo_ov_smul_eq
-- name    : PI.FinKW.LocTo.ov_smul_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:58.7689+00:00
-- url     : https://prove2.me/theorems/81441812-8599-4276-8e9c-18dc722787e3
-- title:
--   Loc To: ov smul eq
-- statement:
--   The Loc To construction uses the ov smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L26-L34

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

theorem PI.FinKW.LocTo.ov_smul_eq (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • t = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) * t := by sorry
