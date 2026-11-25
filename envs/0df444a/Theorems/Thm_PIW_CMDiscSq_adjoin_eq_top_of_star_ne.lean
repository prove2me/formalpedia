-- Prove2me | Theorems.Thm_PIW_CMDiscSq_adjoin_eq_top_of_star_ne
-- name    : PIW.CMDiscSq.adjoin_eq_top_of_star_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:22.218224+00:00
-- url     : https://prove2.me/theorems/b20ccfa5-3fb6-40cb-8532-bbb86889fcb1
-- title:
--   CMDisc Sq: adjoin eq top of star ne
-- statement:
--   The CMDisc Sq construction uses the adjoin eq top of star ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/AdjoinEqTopOfStarNe.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/AdjoinEqTopOfStarNe.lean#L14-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_AdjoinEqTopOfStarNe
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

theorem PIW.CMDiscSq.adjoin_eq_top_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    Algebra.adjoin F {x} = ⊤ := by sorry
