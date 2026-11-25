-- Prove2me | Theorems.Thm_PI_UConjT_blk_castSucc_last
-- name    : PI.UConjT.blk_castSucc_last
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:05.17702+00:00
-- url     : https://prove2.me/theorems/5b32fd39-db7a-4bef-8044-ee5c7d2263eb
-- title:
--   UConj T: blk cast Succ last
-- statement:
--   The UConj T construction uses the blk cast Succ last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L18-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix

theorem PI.UConjT.blk_castSucc_last (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.last n) = 0 := by sorry
