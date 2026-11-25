-- Prove2me | Theorems.Thm_PI_Tr_mem_dualLat
-- name    : PI.Tr.mem_dualLat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:28:24.422555+00:00
-- url     : https://prove2.me/theorems/e2fcb626-e1ed-403f-94e3-35be7497b81f
-- title:
--   Tr: mem dual Lat
-- statement:
--   The Tr construction uses the mem dual Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/DualTransport.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/DualTransport.lean#L26-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped Real
noncomputable section
open PI PI.Tr

theorem PI.Tr.mem_dualLat {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Λ : Submodule ℤ E}
    {y : E} : y ∈ dualLat Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ) := by sorry
