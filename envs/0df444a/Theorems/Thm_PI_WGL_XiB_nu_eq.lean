-- Prove2me | Theorems.Thm_PI_WGL_XiB_nu_eq
-- name    : PI.WGL.XiB.nu_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:46:38.157294+00:00
-- url     : https://prove2.me/theorems/4235f5fb-cb68-4008-ae12-036e25613250
-- title:
--   Xi B: nu eq
-- statement:
--   The Xi B construction uses the nu eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L231-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L231-L261

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

theorem PI.WGL.XiB.nu_eq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin N) :
    (∑ i : Fin n, ((aa h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0)) : ℕ) = lam.natW t := by sorry
