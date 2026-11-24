-- Prove2me | Theorems.Thm_PI_KLW_Rp_of_isIntegral
-- name    : PI.KLW.Rp_of_isIntegral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:35.900166+00:00
-- url     : https://prove2.me/theorems/78a1d7cd-a359-46cc-9477-d80cf2ea8fde
-- title:
--   KLW: Rp of is Integral
-- statement:
--   The KLW construction uses the Rp of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L19-L20

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

theorem PI.KLW.Rp_of_isIntegral {p : ℕ} {x : K} (h : IsIntegral ℤ x) : Rp K p x := by sorry
