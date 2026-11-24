-- Prove2me | Theorems.Thm_PI_KLW_mem_range_iff
-- name    : PI.KLW.mem_range_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:23.795652+00:00
-- url     : https://prove2.me/theorems/5798f153-38b5-40ab-9ad4-de326c2731af
-- title:
--   KLW: mem range iff
-- statement:
--   The KLW construction uses the mem range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L12-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K]

theorem PI.KLW.mem_range_iff {x : K} : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by sorry
