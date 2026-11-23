-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_ext_coord
-- name    : PI.LevelKSplit.W.NCL.ext_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:49.776389+00:00
-- url     : https://prove2.me/theorems/28752572-3b63-439b-822c-050e04254857
-- title:
--   NCL: ext coord
-- statement:
--   The NCL construction uses the ext coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L120-L124

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
variable {D : Dat A n r}
variable (H : D.Hyp)
include H

theorem PI.LevelKSplit.W.NCL.ext_coord {y y' : n → A} (h1 : pV D y = pV D y')
    (h2 : ∀ c, D.h (D.f c) y = D.h (D.f c) y') (h3 : ∀ c, D.h (D.e c) y = D.h (D.e c) y') :
    y = y' := by sorry
