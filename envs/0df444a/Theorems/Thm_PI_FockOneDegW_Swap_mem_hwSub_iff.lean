-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_mem_hwSub_iff
-- name    : PI.FockOneDegW.Swap.mem_hwSub_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:46.733796+00:00
-- url     : https://prove2.me/theorems/de192568-8b07-44ad-bb0b-d5e25be0494b
-- title:
--   Swap: mem hw Sub iff
-- statement:
--   The Swap construction uses the mem hw Sub iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L16-L20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {m n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem PI.FockOneDegW.Swap.mem_hwSub_iff (act : Mat m n →ₗ[ℂ] Module.End ℂ V) (ν : Ix m n → ℚ) (w : V) :
    w ∈ hwSub act ν ↔ (∀ a, act (Eab a a) w = ((ν a : ℚ) : ℂ) • w) ∧
      ∀ a b, posC a b → act (Eab a b) w = 0 := by sorry
