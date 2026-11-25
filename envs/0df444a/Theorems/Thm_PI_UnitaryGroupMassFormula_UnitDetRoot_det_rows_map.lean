-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_det_rows_map
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.det_rows_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:33:58.095751+00:00
-- url     : https://prove2.me/theorems/4b919081-66a3-48ae-9cc7-fbc447e86d30
-- title:
--   Unit Det Root: det rows map
-- statement:
--   The Unit Det Root construction uses the det rows map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/GlobVol.lean#L25-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.det_rows_map (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w : m → m → ℂ) :
    (Matrix.of fun j => δ (w j)).det = LinearMap.det δ * (Matrix.of w).det := by sorry
