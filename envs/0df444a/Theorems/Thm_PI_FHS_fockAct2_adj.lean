-- Prove2me | Theorems.Thm_PI_FHS_fockAct2_adj
-- name    : PI.FHS.fockAct2_adj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:24.130166+00:00
-- url     : https://prove2.me/theorems/87e3a39c-d70a-4bbb-a59d-da34387849a9
-- title:
--   FHS: fock Act2 adj
-- statement:
--   The FHS construction uses the fock Act2 adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L151-L154

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}

theorem PI.FHS.fockAct2_adj {Z : Mat r s} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct2 p q r s Z P) Q = - fockInner P (fockAct2 p q r s Zᴴ Q) := by sorry
