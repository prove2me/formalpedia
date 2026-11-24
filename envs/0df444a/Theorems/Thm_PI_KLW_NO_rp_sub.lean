-- Prove2me | Theorems.Thm_PI_KLW_NO_rp_sub
-- name    : PI.KLW.NO.rp_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:25.373158+00:00
-- url     : https://prove2.me/theorems/ab484594-7cbb-4cfd-9611-587a2dae8019
-- title:
--   NO: rp sub
-- statement:
--   The NO construction uses the rp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneA.lean#L54-L55

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

theorem PI.KLW.NO.rp_sub {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x - y) := by sorry
