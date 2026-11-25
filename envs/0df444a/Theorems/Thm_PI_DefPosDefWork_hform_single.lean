-- Prove2me | Theorems.Thm_PI_DefPosDefWork_hform_single
-- name    : PI.DefPosDefWork.hform_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:27:14.995148+00:00
-- url     : https://prove2.me/theorems/bb8ef8c2-565e-42e1-9fc0-b01d9fa79591
-- title:
--   Def Pos Def Work: hform single
-- statement:
--   The Def Pos Def Work construction uses the hform single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/SplittingOfExtension.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PositiveDefiniteness/SplittingOfExtension.lean#L65-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PositiveDefiniteness_SplittingOfExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DefPosDefWork
open Matrix ComplexOrder

theorem PI.DefPosDefWork.hform_single {E : Type} [CommRing E] (σ : E →+* E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E)
    (i0 : Fin k) (s : E) :
    hform σ J (Pi.single i0 s) (Pi.single i0 s) = σ s * J i0 i0 * s := by sorry
