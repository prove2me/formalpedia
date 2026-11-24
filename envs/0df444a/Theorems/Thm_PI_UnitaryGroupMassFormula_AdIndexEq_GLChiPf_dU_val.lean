-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_dU_val
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.dU_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:29:56.962076+00:00
-- url     : https://prove2.me/theorems/462770e7-5b5c-4d64-b08f-de94d30811e8
-- title:
--   GLChi Pf: d U val
-- statement:
--   The GLChi Pf construction uses the d U val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean#L64-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.dU_val (D : Fin n → kˣ) :
    ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (D i : k)) := by sorry
