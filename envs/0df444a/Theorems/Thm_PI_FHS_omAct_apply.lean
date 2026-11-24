-- Prove2me | Theorems.Thm_PI_FHS_omAct_apply
-- name    : PI.FHS.omAct_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:12.608789+00:00
-- url     : https://prove2.me/theorems/530ae52f-9ae0-4556-83d8-2f5b765aeb3a
-- title:
--   FHS: om Act apply
-- statement:
--   The FHS construction uses the om Act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L67-L69

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

theorem PI.FHS.omAct_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    omAct p q r s M P = ∑ l, ∑ l', M l l' • omE l l' P := by sorry
