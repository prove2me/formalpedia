-- Prove2me | Theorems.Thm_PIW_CMDiscSq_exists_of_star_eq
-- name    : PIW.CMDiscSq.exists_of_star_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:13.434858+00:00
-- url     : https://prove2.me/theorems/f95dbb35-f0f6-4d52-bda4-2f32170faa82
-- title:
--   CMDisc Sq: exists of star eq
-- statement:
--   The CMDisc Sq construction uses the exists of star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/AdjoinEqTopOfStarNe.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/AdjoinEqTopOfStarNe.lean#L8-L12

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

theorem PIW.CMDiscSq.exists_of_star_eq {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {y : E} (hy : star y = y) :
    ∃ a : F, algebraMap F E a = y := by sorry
