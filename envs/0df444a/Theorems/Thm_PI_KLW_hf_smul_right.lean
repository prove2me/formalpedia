-- Prove2me | Theorems.Thm_PI_KLW_hf_smul_right
-- name    : PI.KLW.hf_smul_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:18.825093+00:00
-- url     : https://prove2.me/theorems/f0947d2b-815c-4c68-804e-1d1774eb74d9
-- title:
--   KLW: hf smul right
-- statement:
--   The KLW construction uses the hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L91-L93

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
variable {K : Type} [Field K] {ι : Type} [Fintype ι] (c : K →+* K)

theorem PI.KLW.hf_smul_right (a : K) (v w : ι → K) : hf c v (a • w) = c a * hf c v w := by sorry
