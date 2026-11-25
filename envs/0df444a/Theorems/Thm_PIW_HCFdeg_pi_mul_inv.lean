-- Prove2me | Theorems.Thm_PIW_HCFdeg_pi_mul_inv
-- name    : PIW.HCFdeg.pi_mul_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:47:10.852032+00:00
-- url     : https://prove2.me/theorems/c08d95fd-2fda-4c12-9e40-6a4721386993
-- title:
--   HCFdeg: pi mul inv
-- statement:
--   The HCFdeg construction uses the pi mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean#L29-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem PIW.HCFdeg.pi_mul_inv (π : G →* (H →L[ℂ] H)) (g h : G) (x : H) : π (g * h) (π h⁻¹ x) = π g x := by sorry
