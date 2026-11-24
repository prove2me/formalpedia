-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_good_mul
-- name    : PI.OddDualWeyl.Hom.good_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:03.628184+00:00
-- url     : https://prove2.me/theorems/061e7a78-ee96-4cb3-ab64-9f156e35d0f1
-- title:
--   Hom: good mul
-- statement:
--   The Hom construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L58-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L58-L69

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

theorem PI.OddDualWeyl.Hom.good_mul {d e : ℤ} {p q : Polynomial (MvPolynomial (Fin k × Fin k) R)}
    (hp : Good wt δ d p) (hq : Good wt δ e q) : Good wt δ (d + e) (p * q) := by sorry
