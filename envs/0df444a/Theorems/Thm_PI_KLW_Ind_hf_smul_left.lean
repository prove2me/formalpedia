-- Prove2me | Theorems.Thm_PI_KLW_Ind_hf_smul_left
-- name    : PI.KLW.Ind.hf_smul_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:42:43.641244+00:00
-- url     : https://prove2.me/theorems/da8d4d26-df4d-4b7a-84d4-4e562d1222a7
-- title:
--   Ind: hf smul left
-- statement:
--   The Ind construction uses the hf smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L71-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
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
open PI PI.KLW PI.KLW.Ind
open PI.KLW

theorem PI.KLW.Ind.hf_smul_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (k : K)
    (v w : ι → K) : hf c (k • v) w = k * hf c v w := by sorry
