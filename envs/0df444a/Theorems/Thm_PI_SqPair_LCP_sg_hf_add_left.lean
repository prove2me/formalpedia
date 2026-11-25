-- Prove2me | Theorems.Thm_PI_SqPair_LCP_sg_hf_add_left
-- name    : PI.SqPair.LCP.sg_hf_add_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:04.985698+00:00
-- url     : https://prove2.me/theorems/0d6a5672-af69-5e4e-9e5f-4c48b19ec129
-- title:
--   LCP: sg hf add left
-- statement:
--   The LCP construction uses the sg hf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/StepGlue.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/StepGlue.lean#L12-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
variable {R : Type} [CommRing R] [StarRing R] {ι : Type} [Fintype ι]

theorem PI.SqPair.LCP.sg_hf_add_left (A : Matrix ι ι R) (x x' y : ι → R) :
    hf A (x + x') y = hf A x y + hf A x' y := by sorry
