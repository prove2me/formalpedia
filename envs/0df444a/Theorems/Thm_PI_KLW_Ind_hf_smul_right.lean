-- Prove2me | Theorems.Thm_PI_KLW_Ind_hf_smul_right
-- name    : PI.KLW.Ind.hf_smul_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:04.273876+00:00
-- url     : https://prove2.me/theorems/2fa95561-d214-4063-a44f-b0fa4fdbe2b9
-- title:
--   Ind: hf smul right
-- statement:
--   The Ind construction uses the hf smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L75-L78

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

theorem PI.KLW.Ind.hf_smul_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (k : K)
    (v w : ι → K) : hf c v (k • w) = c k * hf c v w := by sorry
