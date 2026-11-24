-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_sum_emb
-- name    : PI.UnitaryCorollaryDerivatives.DjC.sum_emb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:46:34.298072+00:00
-- url     : https://prove2.me/theorems/4e1e9422-2978-424e-9763-4fcbb4d46c02
-- title:
--   Dj C: sum emb
-- statement:
--   The Dj C construction uses the sum emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L58-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumEqSumCompEmbedding
import Definitions.Def_Lemmata_B110_ExistsMoved
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
variable {N j : ℕ}

theorem PI.UnitaryCorollaryDerivatives.DjC.sum_emb (e : Fin j ↪ Fin N) (f : Fin N → ℂ) (hf : ∀ c, c ∉ Set.range e → f c = 0) :
    ∑ c, f c = ∑ a, f (e a) := by sorry
