-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_lpMinor_tot
-- name    : PI.OddDualWeyl.Hom.lpMinor_tot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:15.077207+00:00
-- url     : https://prove2.me/theorems/30ccddb7-b394-42f8-b039-7234fee3272b
-- title:
--   Hom: lp Minor tot
-- statement:
--   The Hom construction uses the lp Minor tot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L167-L173

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}

theorem PI.OddDualWeyl.Hom.lpMinor_tot (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) :
    IsWeightedHomogeneous (1 : Fin k × Fin k → ℕ) (lpMinor R s hr hn) s := by sorry
