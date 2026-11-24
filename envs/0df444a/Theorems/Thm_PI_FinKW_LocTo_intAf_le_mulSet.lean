-- Prove2me | Theorems.Thm_PI_FinKW_LocTo_intAf_le_mulSet
-- name    : PI.FinKW.LocTo.intAf_le_mulSet
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:34:28.777274+00:00
-- url     : https://prove2.me/theorems/c34bd118-6835-4f17-82b3-77d77b21c318
-- title:
--   Loc To: int Af le mul Set
-- statement:
--   The Loc To construction uses the int Af le mul Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteAdelicComparison/AdelicLatticeToLocalLattices.lean#L86-L98

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

theorem PI.FinKW.LocTo.intAf_le_mulSet (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.S.IntAf I.F I.E ≤ mulSet I v := by sorry
