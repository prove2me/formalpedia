-- Prove2me | Theorems.Thm_PIW_CMDiscSq_sub_mem_differentIdeal
-- name    : PIW.CMDiscSq.sub_mem_differentIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:48:12.342805+00:00
-- url     : https://prove2.me/theorems/39ba5adc-3ac0-4a51-8c34-b6119294056b
-- title:
--   CMDisc Sq: sub mem different Ideal
-- statement:
--   The CMDisc Sq construction uses the sub mem different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/SubMemDifferentIdeal.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/SubMemDifferentIdeal.lean#L8-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_SubMemDifferentIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open PIW PIW.CMDiscSq

theorem PIW.CMDiscSq.sub_mem_differentIdeal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (θ t : 𝓞 E)
    (ht : algebraMap (𝓞 E) E t = star (algebraMap (𝓞 E) E θ)) (hne : θ - t ≠ 0) :
    θ - t ∈ differentIdeal (𝓞 F) (𝓞 E) := by sorry
