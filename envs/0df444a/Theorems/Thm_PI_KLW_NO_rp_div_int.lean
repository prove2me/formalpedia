-- Prove2me | Theorems.Thm_PI_KLW_NO_rp_div_int
-- name    : PI.KLW.NO.rp_div_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:15.574809+00:00
-- url     : https://prove2.me/theorems/f79134c9-5b46-481b-b5b1-d3b8c6c47a7f
-- title:
--   NO: rp div int
-- statement:
--   The NO construction uses the rp div int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L136-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L136-L148

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

theorem PI.KLW.NO.rp_div_int {y : K} (hy : y ∈ (algebraMap (𝓞 K) K).range) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m)
    (hp : p.Prime) : Rp K p (y / m) := by sorry
