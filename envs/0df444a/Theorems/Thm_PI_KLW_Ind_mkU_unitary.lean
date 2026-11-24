-- Prove2me | Theorems.Thm_PI_KLW_Ind_mkU_unitary
-- name    : PI.KLW.Ind.mkU_unitary
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:29.459855+00:00
-- url     : https://prove2.me/theorems/a82d0ccd-36df-4e6b-9d15-e5bb58ed69ca
-- title:
--   Ind: mk U unitary
-- statement:
--   The Ind construction uses the mk U unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/IndBasic.lean#L146-L149

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

theorem PI.KLW.Ind.mkU_unitary {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι]
    (f : (ι → K) →ₗ[K] (ι → K)) (hf' : ∀ v w, hf c (f v) (f w) = hf c v w) :
    IsUnitary c (mkU c f hf') := by sorry
