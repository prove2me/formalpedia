-- Prove2me | Theorems.Thm_PI_OmLocU_Nrm_near_root
-- name    : PI.OmLocU.Nrm.near_root
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:16:02.482803+00:00
-- url     : https://prove2.me/theorems/1b51efc5-4b68-4304-8897-aa37e38ecad7
-- title:
--   Nrm: near root
-- statement:
--   The Nrm construction uses the near root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/NormLeOfNear.lean#L16-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/NormLeOfNear.lean#L16-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LandherrUnitNorm_UnitNormLoc
import Definitions.Def_Lemmata_GeneralBFactLeft_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_NormLeOfNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PI.Landherr₃
open PI PI.OmLocU PI.OmLocU.Nrm

theorem PI.OmLocU.Nrm.near_root {K : Type} [NormedField K] [IsUltrametricDist K] (α β γ y₀ y : K)
    (hg : ‖2 * α * y₀ + β‖ = 1) (hf : ‖α * y₀ ^ 2 + β * y₀ + γ‖ < 1) (hy : α * y ^ 2 + β * y + γ = 0) :
    ∃ z, α * z ^ 2 + β * z + γ = 0 ∧ ‖z - y₀‖ < 1 := by sorry
