-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_gm_mul
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.QRG.gm_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:46.257326+00:00
-- url     : https://prove2.me/theorems/53005c7f-6a64-4c20-bb63-6ffb04e3b6d9
-- title:
--   QRG: gm mul
-- statement:
--   The QRG construction uses the gm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L225-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L225-L225

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.QRG.gm_mul (g g' : UJ σ J) : gm σ J (g * g') = gm σ J g * gm σ J g' := by sorry
