-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_sL_apply
-- name    : PI.LevelKSplit.W.NCH.sL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:18.968262+00:00
-- url     : https://prove2.me/theorems/525bc395-be3a-4c28-a555-260ec7ddbd78
-- title:
--   NCH: s L apply
-- statement:
--   The NCH construction uses the s L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnipotentRadicalActionFormula.lean#L38-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
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
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

theorem PI.LevelKSplit.W.NCH.sL_apply (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + ∑ a, D.h (D.e a) v • uv D half y a - ∑ b, D.h (y b) v • D.e b := by sorry
