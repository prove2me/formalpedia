-- Prove2me | Theorems.Thm_PI_VolNzeroOne_W_tupH_alt
-- name    : PI.VolNzeroOne.W.tupH_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:14.210268+00:00
-- url     : https://prove2.me/theorems/27711f8f-e032-4ac9-875f-ac0875241dd4
-- title:
--   W: tup H alt
-- statement:
--   The W construction uses the tup H alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NilpotentVolumeOne/LinearIndependentFrameWithNormal.lean#L64-L65

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

theorem PI.VolNzeroOne.W.tupH_alt {M r : ℕ} (P : Frame E M r) : tupH P (Fin.castAdd r (Fin.last r)) = P.z := by sorry
