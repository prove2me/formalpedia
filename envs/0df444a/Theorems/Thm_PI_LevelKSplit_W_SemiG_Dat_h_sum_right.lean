-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_sum_right
-- name    : PI.LevelKSplit.W.SemiG.Dat.h_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:17:24.288855+00:00
-- url     : https://prove2.me/theorems/778fc9d2-19ac-4dfc-bf3f-a7d962c8a7b4
-- title:
--   Dat: h sum right
-- statement:
--   The Dat construction uses the h sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiGen.lean#L44-L45

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable (D : Dat A n r)

theorem PI.LevelKSplit.W.SemiG.Dat.h_sum_right {ι : Type} (s : Finset ι) (x : n → A) (y : ι → n → A) :
    D.h x (∑ i ∈ s, y i) = ∑ i ∈ s, D.h x (y i) := by sorry
