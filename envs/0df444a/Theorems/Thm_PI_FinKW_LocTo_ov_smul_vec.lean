-- Prove2me | Theorems.Thm_PI_FinKW_LocTo_ov_smul_vec
-- name    : PI.FinKW.LocTo.ov_smul_vec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:05.813427+00:00
-- url     : https://prove2.me/theorems/dc66bf03-2153-4ddd-96da-b4be61bc43bd
-- title:
--   Loc To: ov smul vec
-- statement:
--   The Loc To construction uses the ov smul vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L36-L40

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

theorem PI.FinKW.LocTo.ov_smul_vec (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : v.adicCompletionIntegers I.F)
    (z : Fin I.n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :
    c • z = ((c : v.adicCompletion I.F) ⊗ₜ[I.F] (1 : I.E)) • z := by sorry
