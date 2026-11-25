-- Prove2me | Theorems.Thm_PI_WGL_XiB_teleM
-- name    : PI.WGL.XiB.teleM
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:47:08.139839+00:00
-- url     : https://prove2.me/theorems/90736a49-ba97-47aa-855d-47ba797d767c
-- title:
--   Xi B: tele M
-- statement:
--   The Xi B construction uses the tele M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L21-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.XiB.teleM {G : Type*} [CommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 1) (w : G) (ℓ σ : ℕ → ℤ) :
    (P n * w) ^ ℓ n * ∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) =
    (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
      w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by sorry
