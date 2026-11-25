-- Prove2me | Theorems.Thm_PIW_CMDiscSq_minpoly_eq_of_star_ne
-- name    : PIW.CMDiscSq.minpoly_eq_of_star_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:46.282929+00:00
-- url     : https://prove2.me/theorems/1d5b2f78-b98b-4f02-ad42-e55b60b73344
-- title:
--   CMDisc Sq: minpoly eq of star ne
-- statement:
--   The CMDisc Sq construction uses the minpoly eq of star ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/AdjoinEqTopOfStarNe.lean#L34-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/AdjoinEqTopOfStarNe.lean#L34-L56

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

theorem PIW.CMDiscSq.minpoly_eq_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    [FiniteDimensional F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    ∃ s n : F, algebraMap F E s = x + star x ∧ algebraMap F E n = x * star x ∧
      minpoly F x = X ^ 2 - C s * X + C n := by sorry
