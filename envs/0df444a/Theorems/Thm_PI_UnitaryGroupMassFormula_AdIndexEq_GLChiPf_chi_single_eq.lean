-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_single_eq
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_single_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:47.709717+00:00
-- url     : https://prove2.me/theorems/95cf7d27-2390-4adf-b2ba-096bdb9a9ce6
-- title:
--   GLChi Pf: chi single eq
-- statement:
--   The GLChi Pf construction uses the chi single eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/GLDelta.lean#L99-L103

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_single_eq (χ : GL (Fin n) k →* ℚ) (i j : Fin n) (d : kˣ) :
    χ (dU (Pi.mulSingle i d)) = χ (dU (Pi.mulSingle j d)) := by sorry
