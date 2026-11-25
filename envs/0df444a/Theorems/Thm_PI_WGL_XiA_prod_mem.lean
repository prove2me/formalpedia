-- Prove2me | Theorems.Thm_PI_WGL_XiA_prod_mem
-- name    : PI.WGL.XiA.prod_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:46:37.736003+00:00
-- url     : https://prove2.me/theorems/5bcbbc18-1ee5-4014-80fe-5f3ea8834ce1
-- title:
--   Xi A: prod mem
-- statement:
--   The Xi A construction uses the prod mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L189-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/RowsZStrictMono.lean#L189-L198

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

theorem PI.WGL.XiA.prod_mem {N : ℕ} {ι : Type*} (s : Finset ι) (ν : ι → Fin N → ℕ) (f : ι → MvPolynomial (Fin N × Fin N) ℂ)
    (hf : ∀ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν i)) :
    ∏ i ∈ s, f i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (∑ i ∈ s, ν i) := by sorry
