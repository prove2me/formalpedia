-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_good_pow
-- name    : PI.OddDualWeyl.Hom.good_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:35:40.604993+00:00
-- url     : https://prove2.me/theorems/c0db4a57-3b77-42fc-b01b-31be5f7d7ac7
-- title:
--   Hom: good pow
-- statement:
--   The Hom construction uses the good pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L71-L77

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

theorem PI.OddDualWeyl.Hom.good_pow {d : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (hp : Good wt δ d p)
    (m : ℕ) : Good wt δ (m * d) (p ^ m) := by sorry
