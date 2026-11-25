-- Prove2me | Theorems.Thm_PI_QmIndepW_scalar
-- name    : PI.QmIndepW.scalar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:29:21.687944+00:00
-- url     : https://prove2.me/theorems/f4c96b44-6a25-57fc-99a3-f6e2789b7e66
-- title:
--   Qm Indep W: scalar
-- statement:
--   The Qm Indep W construction uses the scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/QmIndep.lean#L9-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuarticIndependence/QmIndep.lean#L9-L43

import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepPoly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_QmIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex

theorem PI.QmIndepW.scalar (z : Fin 2 × Fin 2 → Fin 2 × Fin 2 → ℂ) (Y Y' : ℂ) (hY : Y' ≠ Y + 1)
    (hz : ∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) * z A B = 0) :
    ∀ A B, z A B = 0 := by sorry
