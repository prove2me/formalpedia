-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_smul_dot
-- name    : PI.UnitaryGroupMassFormula.LCG.DIdx.smul_dot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:45:40.103173+00:00
-- url     : https://prove2.me/theorems/7a8b70ad-10c2-5990-a9f3-53df85d4b2db
-- title:
--   DIdx: smul dot
-- statement:
--   The DIdx construction uses the smul dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean#L89-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
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
open PI.UnitaryGroupMassFormula.LCG.DIdx

theorem PI.UnitaryGroupMassFormula.LCG.DIdx.smul_dot {K : Type} [Field K] [NumberField K] {k : ℕ} (c : 𝓞 K) (x t : Fin k → K) :
    (c • x) ⬝ᵥ t = algebraMap (𝓞 K) K c * (x ⬝ᵥ t) := by sorry
