-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScalDeg_gv_mul
-- name    : PI.UnitaryGroupMassFormula.ScalDeg.gv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:09.063186+00:00
-- url     : https://prove2.me/theorems/bbf67e6c-476d-4a2e-8bff-c609f23aa4af
-- title:
--   Scal Deg: gv mul
-- statement:
--   The Scal Deg construction uses the gv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarDegree/ScalDegMain.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarDegree/ScalDegMain.lean#L31-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg

theorem PI.UnitaryGroupMassFormula.ScalDeg.gv_mul {T : Type} {N N' : ℕ} (s s' : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)
    (k : FrV T N) : gv (fun τ => s τ * s' τ) y' k = C (s k.1) * gv s' y' k := by sorry
