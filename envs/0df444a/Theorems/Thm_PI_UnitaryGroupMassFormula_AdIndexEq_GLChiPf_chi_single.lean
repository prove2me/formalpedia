-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_single
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:23.357464+00:00
-- url     : https://prove2.me/theorems/d360ffe2-d7ec-495f-a8d8-734f413569ca
-- title:
--   GLChi Pf: chi single
-- statement:
--   The GLChi Pf construction uses the chi single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean#L105-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean#L105-L121

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_single (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (i : Fin n) (d : kˣ) : χ (dU (Pi.mulSingle i d)) = 1 := by sorry
