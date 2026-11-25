-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_fix_span
-- name    : PI.LevelKSplit.W.NCH.fix_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:58.420827+00:00
-- url     : https://prove2.me/theorems/538a1c94-1ad6-527b-9a7c-e61289347e7f
-- title:
--   NCH: fix span
-- statement:
--   The NCH construction uses the fix span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L18-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}

theorem PI.LevelKSplit.W.NCH.fix_span {Φ : (n → A) →ₗ[A] (n → A)} (he : ∀ a, Φ (D.e a) = D.e a) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : Φ x = x := by sorry
