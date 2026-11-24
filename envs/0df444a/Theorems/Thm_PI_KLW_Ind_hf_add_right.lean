-- Prove2me | Theorems.Thm_PI_KLW_Ind_hf_add_right
-- name    : PI.KLW.Ind.hf_add_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:02.278564+00:00
-- url     : https://prove2.me/theorems/1e8573d7-643e-4139-bd77-3ea49bac1c79
-- title:
--   Ind: hf add right
-- statement:
--   The Ind construction uses the hf add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L47-L49

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

theorem PI.KLW.Ind.hf_add_right {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (v w w' : ι → K) :
    hf c v (w + w') = hf c v w + hf c v w' := by sorry
