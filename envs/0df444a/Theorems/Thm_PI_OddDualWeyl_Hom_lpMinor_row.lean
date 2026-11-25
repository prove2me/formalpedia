-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_lpMinor_row
-- name    : PI.OddDualWeyl.Hom.lpMinor_row
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:41.457882+00:00
-- url     : https://prove2.me/theorems/11cf38ca-6d8f-42c5-a5ab-beefed266eea
-- title:
--   Hom: lp Minor row
-- statement:
--   The Hom construction uses the lp Minor row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L157-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L157-L165

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

theorem PI.OddDualWeyl.Hom.lpMinor_row (s : ℕ) (hr : s ≤ k) (hn : s ≤ k) (c : Fin k) :
    IsWeightedHomogeneous (rowW c) (lpMinor R s hr hn)
      (∑ p : Fin s, if Fin.castLE hr p = c then 1 else 0) := by sorry
