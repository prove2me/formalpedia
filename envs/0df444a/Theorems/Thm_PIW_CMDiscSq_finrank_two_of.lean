-- Prove2me | Theorems.Thm_PIW_CMDiscSq_finrank_two_of
-- name    : PIW.CMDiscSq.finrank_two_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:05.064061+00:00
-- url     : https://prove2.me/theorems/ecc7e5e2-3a58-4d14-87dd-2c359e3ccda0
-- title:
--   CMDisc Sq: finrank two of
-- statement:
--   The CMDisc Sq construction uses the finrank two of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/FinrankTwoOf.lean#L22-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/FinrankTwoOf.lean#L22-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_FinrankTwoOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open PIW PIW.CMDiscSq

theorem PIW.CMDiscSq.finrank_two_of {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (x : E) (hx : star x ≠ x) :
    finrank F E = 2 := by sorry
