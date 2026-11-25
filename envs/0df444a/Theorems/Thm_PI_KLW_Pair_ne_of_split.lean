-- Prove2me | Theorems.Thm_PI_KLW_Pair_ne_of_split
-- name    : PI.KLW.Pair.ne_of_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:32:47.893937+00:00
-- url     : https://prove2.me/theorems/f68f99d7-dee9-43e2-9c2d-f68a8d8816e5
-- title:
--   Pair: ne of split
-- statement:
--   The Pair construction uses the ne of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L169-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean#L169-L175

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
import Theorems.Thm_PI_KLW_NO_ne_of_split

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
open PI PI.KLW PI.KLW.Pair
open PI.KLW

theorem PI.KLW.Pair.ne_of_split {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ}
    (hs : SplitK c p) : ∃ z, c z ≠ z := by sorry
