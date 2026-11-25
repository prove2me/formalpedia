-- Prove2me | Theorems.Thm_PI_OmLocU_Nrm_ff_binary
-- name    : PI.OmLocU.Nrm.ff_binary
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:41.716997+00:00
-- url     : https://prove2.me/theorems/fad45818-0e60-46b5-a7bb-83c66b832df1
-- title:
--   Nrm: ff binary
-- statement:
--   The Nrm construction uses the ff binary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/NormLeOfNear.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/NormLeOfNear.lean#L12-L14

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

theorem PI.OmLocU.Nrm.ff_binary {k : Type} [Field k] [Fintype k] (t m e : k) (hD : t ^ 2 - 4 * m ≠ 0) :
    ∃ x y : k, x ^ 2 + t * x * y + m * y ^ 2 = e := by sorry
