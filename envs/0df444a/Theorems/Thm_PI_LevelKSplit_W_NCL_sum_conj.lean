-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_sum_conj
-- name    : PI.LevelKSplit.W.NCL.sum_conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:34:24.430243+00:00
-- url     : https://prove2.me/theorems/52ed66d8-573e-4090-9362-09dd31fbcfc1
-- title:
--   NCL: sum conj
-- statement:
--   The NCL construction uses the sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L194-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevLSubPerp.lean#L194-L208

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

theorem PI.LevelKSplit.W.NCL.sum_conj (σ : A →+* A) (U W : Fin r → Fin r → A) (α β : Fin r → A)
    (h : ∀ b c, ∑ a, σ (U a b) * W a c = if b = c then 1 else 0) :
    ∑ a, σ (∑ b, U a b * α b) * ∑ c, W a c * β c = ∑ b, σ (α b) * β b := by sorry
