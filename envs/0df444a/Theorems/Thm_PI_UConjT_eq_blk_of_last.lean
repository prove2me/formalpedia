-- Prove2me | Theorems.Thm_PI_UConjT_eq_blk_of_last
-- name    : PI.UConjT.eq_blk_of_last
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:50.710859+00:00
-- url     : https://prove2.me/theorems/77d99e52-8390-4ba9-ab0f-c3e0215e1097
-- title:
--   UConj T: eq blk of last
-- statement:
--   The UConj T construction uses the eq blk of last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L32-L45

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

theorem PI.UConjT.eq_blk_of_last {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0)
    (hrow : ∀ j, k (Fin.last n) (Fin.castSucc j) = 0) (hll : k (Fin.last n) (Fin.last n) = 1) :
    PI.UMultOne.blk n (k.submatrix Fin.castSucc Fin.castSucc) = k := by sorry
