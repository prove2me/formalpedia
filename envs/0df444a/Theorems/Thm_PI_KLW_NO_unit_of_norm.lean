-- Prove2me | Theorems.Thm_PI_KLW_NO_unit_of_norm
-- name    : PI.KLW.NO.unit_of_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:17.409021+00:00
-- url     : https://prove2.me/theorems/d0e3d40f-4f30-4856-b26b-2d91d3b34c63
-- title:
--   NO: unit of norm
-- statement:
--   The NO construction uses the unit of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L173-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L173-L182

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

theorem PI.KLW.NO.unit_of_norm (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {z : K} (hz : Rp K p z) (hn : ¬ Rp K p (z * c z / p)) :
    z ≠ 0 ∧ Rp K p z⁻¹ := by sorry
