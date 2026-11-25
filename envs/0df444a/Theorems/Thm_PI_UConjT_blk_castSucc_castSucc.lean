-- Prove2me | Theorems.Thm_PI_UConjT_blk_castSucc_castSucc
-- name    : PI.UConjT.blk_castSucc_castSucc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:41.408849+00:00
-- url     : https://prove2.me/theorems/e2527e88-9e21-54d7-bb96-d9b02ed4a533
-- title:
--   UConj T: blk cast Succ cast Succ
-- statement:
--   The UConj T construction uses the blk cast Succ cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L14-L16

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

theorem PI.UConjT.blk_castSucc_castSucc (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.castSucc b) = h a b := by sorry
