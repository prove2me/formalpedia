-- Prove2me | Theorems.Thm_PI_KLW_NO_ne_of_split
-- name    : PI.KLW.NO.ne_of_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:26.109905+00:00
-- url     : https://prove2.me/theorems/5e366af0-eda5-48d7-b743-119b7b42dea7
-- title:
--   NO: ne of split
-- statement:
--   The NO construction uses the ne of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L255-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L255-L260

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

theorem PI.KLW.NO.ne_of_split {K : Type} [Field K] [NumberField K] (c : K →+* K) {p : ℕ} (h : SplitK c p) :
    ∃ z, c z ≠ z := by sorry
