-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_second_projection_split_equiv
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.BrB.second_projection_split_equiv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:42.385507+00:00
-- url     : https://prove2.me/theorems/724f0a07-5f11-5fac-8c65-b021fad375f5
-- title:
--   Br B: second projection split equiv
-- statement:
--   The Br B construction uses the second projection split equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondProjectionSplitEquiv.lean#L44-L45

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.BrB.second_projection_split_equiv {K R : Type} [Field K] [CommRing R] (σ : R →+* R) (p1 : R →+* K)
    (hb : Function.Bijective (piHom σ p1)) (r : R) : SplitGL.p2 (piEquiv σ p1 hb) r = p1 (σ r) := by sorry
