-- Prove2me | Theorems.Thm_PI_OddDualWeyl_Hom_good_congr
-- name    : PI.OddDualWeyl.Hom.good_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:48.245798+00:00
-- url     : https://prove2.me/theorems/f9edca40-7ebc-47fa-bccf-e582c1823d82
-- title:
--   Hom: good congr
-- statement:
--   The Hom construction uses the good congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightMultiplicity.lean#L20-L23

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

theorem PI.OddDualWeyl.Hom.good_congr {d e : ℤ} {p : Polynomial (MvPolynomial (Fin k × Fin k) R)} (h : d = e)
    (hp : Good wt δ d p) : Good wt δ e p := by sorry
