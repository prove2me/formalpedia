-- Prove2me | Theorems.Thm_PI_KLW_Ind_hf_sub_right
-- name    : PI.KLW.Ind.hf_sub_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:34:13.835003+00:00
-- url     : https://prove2.me/theorems/02e99cfd-f376-5181-b2fd-48695d4fc158
-- title:
--   Ind: hf sub right
-- statement:
--   The Ind construction uses the hf sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L55-L57

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

theorem PI.KLW.Ind.hf_sub_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w w' : ι → K) :
    hf c v (w - w') = hf c v w - hf c v w' := by sorry
