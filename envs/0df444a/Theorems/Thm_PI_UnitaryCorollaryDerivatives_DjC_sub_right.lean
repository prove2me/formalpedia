-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_sub_right
-- name    : PI.UnitaryCorollaryDerivatives.DjC.sub_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:43.627833+00:00
-- url     : https://prove2.me/theorems/43cadced-ccca-532a-a33f-8619aba6e5ad
-- title:
--   Dj C: sub right
-- statement:
--   The Dj C construction uses the sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/DjCurveA.lean#L65-L70

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

theorem PI.UnitaryCorollaryDerivatives.DjC.sub_right (e : Fin j ↪ Fin N) (row : Fin j → Fin N) (h E : Matrix (Fin N) (Fin N) ℂ)
    (hE : Pres (Set.range e) E) :
    (Matrix.of fun a b => (h * E) (row a) (e b)) = (Matrix.of fun a b => h (row a) (e b)) * sub e E := by sorry
