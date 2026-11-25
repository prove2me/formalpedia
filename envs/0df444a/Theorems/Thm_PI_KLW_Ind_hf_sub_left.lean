-- Prove2me | Theorems.Thm_PI_KLW_Ind_hf_sub_left
-- name    : PI.KLW.Ind.hf_sub_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:07.404948+00:00
-- url     : https://prove2.me/theorems/ce1f8865-cdda-4209-8fa5-2ffaf9f4bb17
-- title:
--   Ind: hf sub left
-- statement:
--   The Ind construction uses the hf sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L51-L53

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

theorem PI.KLW.Ind.hf_sub_left {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v v' w : ι → K) :
    hf c (v - v') w = hf c v w - hf c v' w := by sorry
