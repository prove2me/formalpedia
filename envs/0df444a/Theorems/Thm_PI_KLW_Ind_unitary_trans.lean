-- Prove2me | Theorems.Thm_PI_KLW_Ind_unitary_trans
-- name    : PI.KLW.Ind.unitary_trans
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:33:45.253471+00:00
-- url     : https://prove2.me/theorems/2b5c79ea-a271-531c-8ff2-befe20c8cf2c
-- title:
--   Ind: unitary trans
-- statement:
--   The Ind construction uses the unitary trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L155-L158

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

theorem PI.KLW.Ind.unitary_trans {K : Type} [Field K] {c : K →+* K} {ι : Type} [Fintype ι]
    {u u' : (ι → K) ≃ₗ[K] (ι → K)} (hu : IsUnitary c u) (hu' : IsUnitary c u') :
    IsUnitary c (u.trans u') := by sorry
