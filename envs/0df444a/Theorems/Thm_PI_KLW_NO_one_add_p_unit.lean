-- Prove2me | Theorems.Thm_PI_KLW_NO_one_add_p_unit
-- name    : PI.KLW.NO.one_add_p_unit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:21.714373+00:00
-- url     : https://prove2.me/theorems/8a046682-7ec8-4f20-a846-86cd0b33d254
-- title:
--   NO: one add p unit
-- statement:
--   The NO construction uses the one add p unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L184-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L184-L197

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
variable {K : Type} [Field K] [NumberField K] {p : ℕ}

theorem PI.KLW.NO.one_add_p_unit (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {r : K} (hr : Rp K p r) :
    (1 + (p : K) * r) ≠ 0 ∧ Rp K p (1 + (p : K) * r)⁻¹ := by sorry
