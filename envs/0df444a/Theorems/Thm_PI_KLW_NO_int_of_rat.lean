-- Prove2me | Theorems.Thm_PI_KLW_NO_int_of_rat
-- name    : PI.KLW.NO.int_of_rat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:06.50341+00:00
-- url     : https://prove2.me/theorems/f55c9ab3-9888-4860-bf1e-c20f614e513f
-- title:
--   NO: int of rat
-- statement:
--   The NO construction uses the int of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L98-L104

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

theorem PI.KLW.NO.int_of_rat {K : Type} [Field K] [NumberField K] (q : ℚ)
    (h : (q : K) ∈ (algebraMap (𝓞 K) K).range) : ∃ m : ℤ, q = m := by sorry
