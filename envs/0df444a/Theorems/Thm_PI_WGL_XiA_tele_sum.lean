-- Prove2me | Theorems.Thm_PI_WGL_XiA_tele_sum
-- name    : PI.WGL.XiA.tele_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:46:59.205932+00:00
-- url     : https://prove2.me/theorems/25c10222-97de-45a3-975e-d29e916accb6
-- title:
--   Xi A: tele sum
-- statement:
--   The Xi A construction uses the tele sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L200-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L200-L217

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_MultisetProdNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiA
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.XiA.tele_sum (ℓ : ℕ → ℤ) (n t : ℕ) (ht : t ≤ n) :
    ∑ i ∈ Finset.range n, (if t ≤ i then ℓ i - ℓ (i + 1) else 0) = ℓ t - ℓ n := by sorry
