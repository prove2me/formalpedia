-- Prove2me | Theorems.Thm_PI_SqPairLocal_RU_exists_conjugation_fixed_uniformizer
-- name    : PI.SqPairLocal.RU.exists_conjugation_fixed_uniformizer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:25:45.866386+00:00
-- url     : https://prove2.me/theorems/ed23fa99-1318-5927-a1d1-547a52354356
-- title:
--   RU: exists conjugation fixed uniformizer
-- statement:
--   The RU construction uses the exists conjugation fixed uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsConjugationFixedUniformizer.lean#L17-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/ExistsConjugationFixedUniformizer.lean#L17-L54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_MemFixSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsConjugationFixedUniformizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal PI.SqPairLocal.RU
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.RU.exists_conjugation_fixed_uniformizer (hE : PI.IsCMUnram E) (Q : Ideal (𝓞 E)) (hQ : Q.IsMaximal)
    (hc : Q.comap (cj E) = Q) : ∃ ϖ : 𝓞 E, cj E ϖ = ϖ ∧ ϖ ∈ Q ∧ ϖ ∉ Q ^ 2 := by sorry
