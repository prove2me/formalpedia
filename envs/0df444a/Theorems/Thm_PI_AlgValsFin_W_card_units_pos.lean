-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_card_units_pos
-- name    : PI.AlgValsFin.W.card_units_pos
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:36.082311+00:00
-- url     : https://prove2.me/theorems/c5d452d9-785d-49d2-972a-25b2774e8ec7
-- title:
--   W: card units pos
-- statement:
--   The W construction uses the card units pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/PowCardSubOneMem.lean#L46-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem PI.AlgValsFin.W.card_units_pos (n : ℕ) : 0 < Nat.card ((𝓞 L ⧸ v.asIdeal ^ n)ˣ) := by sorry
