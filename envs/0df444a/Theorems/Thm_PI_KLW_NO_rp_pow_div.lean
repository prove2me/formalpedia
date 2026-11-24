-- Prove2me | Theorems.Thm_PI_KLW_NO_rp_pow_div
-- name    : PI.KLW.NO.rp_pow_div
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:11.584728+00:00
-- url     : https://prove2.me/theorems/c50a549a-a307-47b1-aabb-200f69c248a2
-- title:
--   NO: rp pow div
-- statement:
--   The NO construction uses the rp pow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L231-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L231-L247

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

theorem PI.KLW.NO.rp_pow_div (hp : p.Prime) {Q : ℕ} (hQ : Q ≠ 0) {k : ℕ} (hk : Q ≤ k) :
    Rp K p ((p : K) ^ k / Q) := by sorry
