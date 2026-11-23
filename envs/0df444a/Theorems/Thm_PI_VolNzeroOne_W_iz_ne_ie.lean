-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_iz_ne_ie
-- name    : PI.VolNzeroOne.W.iz_ne_ie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:27.975803+00:00
-- url     : https://prove2.me/theorems/0ce4a826-bf69-44ae-b98f-97cda6b0d2a1
-- title:
--   W: iz ne ie
-- statement:
--   The W construction uses the iz ne ie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L70-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolNzeroOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NilpotentVolumeOne_LinearIndependentFrameWithNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolNzeroOne PI.VolNzeroOne.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem PI.VolNzeroOne.W.iz_ne_ie {r : ℕ} (a : Fin r) :
    (Fin.castAdd r (Fin.last r) : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.castSucc a) := by sorry
