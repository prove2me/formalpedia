-- Prove2me | Theorems.Thm_PI_Residue_norm_eq_cof
-- name    : PI.Residue.norm_eq_cof
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:17.589679+00:00
-- url     : https://prove2.me/theorems/d4c0d62d-f71c-4908-a7f4-5c4013485a4d
-- title:
--   Residue: norm eq cof
-- statement:
--   The Residue construction uses the norm eq cof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/DvdSpanOfIdealSet.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/DvdSpanOfIdealSet.lean#L44-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_DvdSpanOfIdealSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]

theorem PI.Residue.norm_eq_cof (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    mixedEmbedding.norm (x : mixedSpace K) =
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) * (Ideal.absNorm (cof J x) : ℝ) := by sorry
