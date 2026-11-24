-- Prove2me | Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_alg_int_mem
-- name    : PI.ScPsiExists.UnitaryGroupMassFormula.alg_int_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:57.804961+00:00
-- url     : https://prove2.me/theorems/1f380414-ae6b-46ef-a24e-cd89812e541d
-- title:
--   Unitary Group Mass Formula: alg int mem
-- statement:
--   The Unitary Group Mass Formula construction uses the alg int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean#L84-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula

theorem PI.ScPsiExists.UnitaryGroupMassFormula.alg_int_mem (F : Type) [Field F] [NumberField F] (d : 𝓞 F) :
    algebraMap F (Af F) (algebraMap (𝓞 F) F d) ∈ Formalism.UG.intAd F := by sorry
