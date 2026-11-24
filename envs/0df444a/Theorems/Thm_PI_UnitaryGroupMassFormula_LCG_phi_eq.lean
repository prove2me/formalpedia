-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_phi_eq
-- name    : PI.UnitaryGroupMassFormula.LCG.phi_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:39.897117+00:00
-- url     : https://prove2.me/theorems/6c069f6c-e890-4ce5-a746-ba1bbdd9e9bf
-- title:
--   LCG: phi eq
-- statement:
--   The LCG construction uses the phi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean#L38-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.LatCountG

theorem PI.UnitaryGroupMassFormula.LCG.phi_eq (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (γ : I.GFset) (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat ((x⁻¹ * (γ : I.GA) * y).1 v) = amat I x y v (gm I γ) := by sorry
