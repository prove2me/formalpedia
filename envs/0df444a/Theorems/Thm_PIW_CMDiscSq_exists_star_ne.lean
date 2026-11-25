-- Prove2me | Theorems.Thm_PIW_CMDiscSq_exists_star_ne
-- name    : PIW.CMDiscSq.exists_star_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:53.927782+00:00
-- url     : https://prove2.me/theorems/7cd8cae5-22d0-424c-924c-1f38f6ba3d45
-- title:
--   CMDisc Sq: exists star ne
-- statement:
--   The CMDisc Sq construction uses the exists star ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/FinrankTwoOf.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/FinrankTwoOf.lean#L10-L20

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

theorem PIW.CMDiscSq.exists_star_ne {E : Type} [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ x : E, star x ≠ x := by sorry
