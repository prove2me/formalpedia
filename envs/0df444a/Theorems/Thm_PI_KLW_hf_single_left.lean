-- Prove2me | Theorems.Thm_PI_KLW_hf_single_left
-- name    : PI.KLW.hf_single_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:33:19.100736+00:00
-- url     : https://prove2.me/theorems/e12827a1-80a5-46a4-8485-eb6c397d4b98
-- title:
--   KLW: hf single left
-- statement:
--   The KLW construction uses the hf single left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/RpOfIsIntegral.lean#L101-L103

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

theorem PI.KLW.hf_single_left [DecidableEq ι] (i : ι) (a : K) (w : ι → K) :
    hf c (Pi.single i a) w = a * c (w i) := by sorry
