-- Prove2me | Theorems.Thm_PI_KLW_hf_smul_left
-- name    : PI.KLW.hf_smul_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:31.024374+00:00
-- url     : https://prove2.me/theorems/6f3e7873-19ef-42db-b24c-1ef1836e7956
-- title:
--   KLW: hf smul left
-- statement:
--   The KLW construction uses the hf smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L88-L89

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

theorem PI.KLW.hf_smul_left (a : K) (v w : ι → K) : hf c (a • v) w = a * hf c v w := by sorry
