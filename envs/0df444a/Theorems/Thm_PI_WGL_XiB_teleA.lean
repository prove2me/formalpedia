-- Prove2me | Theorems.Thm_PI_WGL_XiB_teleA
-- name    : PI.WGL.XiB.teleA
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:59:38.86309+00:00
-- url     : https://prove2.me/theorems/409e6060-1227-5813-bba3-2124c4971cc6
-- title:
--   Xi B: tele A
-- statement:
--   The Xi B construction uses the tele A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L9-L19

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

theorem PI.WGL.XiB.teleA {G : Type*} [AddCommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 0) (w : G) (ℓ σ : ℕ → ℤ) :
    ℓ n • (P n + w) + ∑ i ∈ Finset.range n, ((σ i - ℓ (i + 1)) • P (i + 1) + (ℓ i - σ i) • (P i + w)) =
    (∑ j ∈ Finset.range n, σ j • (P (j + 1) - P j)) +
      ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) • w := by sorry
