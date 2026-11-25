-- Prove2me | Theorems.Thm_PI_KLW_NO_inv_of_fixed
-- name    : PI.KLW.NO.inv_of_fixed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:33:02.555903+00:00
-- url     : https://prove2.me/theorems/d17c09e8-c6df-4aa3-aa4d-d4af422b64a1
-- title:
--   NO: inv of fixed
-- statement:
--   The NO construction uses the inv of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L150-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L150-L171

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

theorem PI.KLW.NO.inv_of_fixed (c : K →+* K) (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) (hp : p.Prime)
    {x : K} (hx : Rp K p x) (hfix : c x = x) (hnp : ¬ Rp K p (x / p)) : x ≠ 0 ∧ Rp K p x⁻¹ := by sorry
