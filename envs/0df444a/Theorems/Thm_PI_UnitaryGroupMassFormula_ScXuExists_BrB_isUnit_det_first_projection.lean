-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_isUnit_det_first_projection
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrB.isUnit_det_first_projection
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:40:45.055888+00:00
-- url     : https://prove2.me/theorems/847efccd-45e9-4bfa-8a6e-1c275c3c2fb7
-- title:
--   Br B: is Unit det first projection
-- statement:
--   The Br B construction uses the is Unit det first projection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean#L51-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrB.isUnit_det_first_projection {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (π : R ≃+* k × k) (J : Matrix n n R) (hdet : IsUnit J.det) : IsUnit (J.map (SplitGL.p1 π)).det := by sorry
