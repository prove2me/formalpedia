-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SchurClosable_Main_alg
-- name    : PI.UnitaryGroupMassFormula.SchurClosable.Main.alg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:36.12673+00:00
-- url     : https://prove2.me/theorems/134894f1-5833-4f33-b10b-8f9a1bd5f415
-- title:
--   Main: alg
-- statement:
--   The Main construction uses the alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurUnitaryInner/UnitaryInner.lean#L12-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurUnitaryInner/UnitaryInner.lean#L12-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SchurClosable PI.UnitaryGroupMassFormula.SchurClosable.Main
open Filter Topology

theorem PI.UnitaryGroupMassFormula.SchurClosable.Main.alg {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (D : Submodule ℂ H) (A : D →ₗ[ℂ] H') (a : ℂ)
    (hK : ∀ x y : D,
      inner ℂ (x : H) (y : H) = a * (inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y))) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H) := by sorry
