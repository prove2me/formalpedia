-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_H_sub_left
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_sub_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:47.410971+00:00
-- url     : https://prove2.me/theorems/1f29f867-e400-44e2-ac7d-3828fa1affff
-- title:
--   QRG: H sub left
-- statement:
--   The QRG construction uses the H sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L54-L55

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)

theorem PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_sub_left (x y z : Fin n → K) : H σ J (x - y) z = H σ J x z - H σ J y z := by sorry
