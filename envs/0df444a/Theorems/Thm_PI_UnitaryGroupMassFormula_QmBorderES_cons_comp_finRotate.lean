-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_cons_comp_finRotate
-- name    : PI.UnitaryGroupMassFormula.QmBorderES.cons_comp_finRotate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:34.341916+00:00
-- url     : https://prove2.me/theorems/b66fb400-2aaa-47df-accc-9b982a88bbcd
-- title:
--   Qm Border ES: cons comp fin Rotate
-- statement:
--   The Qm Border ES construction uses the cons comp fin Rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L17-L22

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES

theorem PI.UnitaryGroupMassFormula.QmBorderES.cons_comp_finRotate {n t : ℕ} (e : Fin n) (f : Fin t → Fin n) :
    PI.bE e f ∘ (finRotate (t + 1) : Fin (t + 1) → Fin (t + 1)) = PI.bS f e := by sorry
