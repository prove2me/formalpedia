-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_det_sub_noninj
-- name    : PI.UnitaryGroupMassFormula.DSIC.det_sub_noninj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:40:04.628742+00:00
-- url     : https://prove2.me/theorems/c286d291-5b35-4ffc-9ea6-3364f8a21eb6
-- title:
--   DSIC: det sub noninj
-- statement:
--   The DSIC construction uses the det sub noninj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/QuasiDeterminantConjInv.lean#L61-L64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix

theorem PI.UnitaryGroupMassFormula.DSIC.det_sub_noninj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) (hc : ¬ Function.Injective c) :
    (A.submatrix id c).det = 0 := by sorry
