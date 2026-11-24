-- Prove2me | Theorems.Thm_PI_KLW_NO_intCast_mem_O
-- name    : PI.KLW.NO.intCast_mem_O
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:13.33315+00:00
-- url     : https://prove2.me/theorems/2eb7dd56-8713-4276-8175-6d2d6271a5c2
-- title:
--   NO: int Cast mem O
-- statement:
--   The NO construction uses the int Cast mem O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L23-L24

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

theorem PI.KLW.NO.intCast_mem_O {K : Type} [Field K] [NumberField K] (n : ℤ) :
    (n : K) ∈ (algebraMap (𝓞 K) K).range := by sorry
