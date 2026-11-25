-- Prove2me | Theorems.Thm_PI_OmLocU_Nrm_norm_le_of_near
-- name    : PI.OmLocU.Nrm.norm_le_of_near
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:30.057988+00:00
-- url     : https://prove2.me/theorems/a923fa22-ca5d-4f50-97b7-fa7eff60aac0
-- title:
--   Nrm: norm le of near
-- statement:
--   The Nrm construction uses the norm le of near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/NormLeOfNear.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/NormLeOfNear.lean#L63-L66

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

theorem PI.OmLocU.Nrm.norm_le_of_near {K : Type} [NormedField K] [IsUltrametricDist K] {z y₀ : K} (h : ‖z - y₀‖ < 1)
    (h0 : ‖y₀‖ ≤ 1) : ‖z‖ ≤ 1 := by sorry
