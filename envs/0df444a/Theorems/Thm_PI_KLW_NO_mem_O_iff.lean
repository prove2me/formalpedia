-- Prove2me | Theorems.Thm_PI_KLW_NO_mem_O_iff
-- name    : PI.KLW.NO.mem_O_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:08.124796+00:00
-- url     : https://prove2.me/theorems/96d30c79-f00f-450f-8bc3-85ee0d6655f2
-- title:
--   NO: mem O iff
-- statement:
--   The NO construction uses the mem O iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
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
open PI PI.KLW PI.KLW.NO

theorem PI.KLW.NO.mem_O_iff {K : Type} [Field K] [NumberField K] {x : K} :
    x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by sorry
