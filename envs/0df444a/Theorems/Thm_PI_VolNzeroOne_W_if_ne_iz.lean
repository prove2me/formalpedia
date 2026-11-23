-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_if_ne_iz
-- name    : PI.VolNzeroOne.W.if_ne_iz
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:36.202768+00:00
-- url     : https://prove2.me/theorems/07b14986-d7cd-4f3a-83e9-e4635cde31de
-- title:
--   W: if ne iz
-- statement:
--   The W construction uses the if ne iz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L84-L89

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

theorem PI.VolNzeroOne.W.if_ne_iz {r : ℕ} (a : Fin r) :
    (Fin.natAdd (r + 1) a : Fin (r + 1 + r)) ≠ Fin.castAdd r (Fin.last r) := by sorry
