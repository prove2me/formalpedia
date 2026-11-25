-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Loc_mulVec_span_stable
-- name    : PI.LevelKSplit.W.Loc.mulVec_span_stable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:43.051998+00:00
-- url     : https://prove2.me/theorems/f3833cbd-edac-4a80-87a9-3276b0f6956b
-- title:
--   Loc: mul Vec span stable
-- statement:
--   The Loc construction uses the mul Vec span stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean#L26-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}

theorem PI.LevelKSplit.W.Loc.mulVec_span_stable (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ x ∈ G, A.mulVec x ∈ span O G) : ∀ x ∈ span O G, A.mulVec x ∈ span O G := by sorry
