-- Prove2me | Theorems.Thm_PIW_HCFdeg_integrable_cf
-- name    : PIW.HCFdeg.integrable_cf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:49:44.897011+00:00
-- url     : https://prove2.me/theorems/4cad6740-203a-5291-8707-7c745b7c68de
-- title:
--   HCFdeg: integrable cf
-- statement:
--   The HCFdeg construction uses the integrable cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean#L42-L44

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
variable [MeasurableSpace G] {μ : Measure G}

theorem PIW.HCFdeg.integrable_cf (π : G →* (H →L[ℂ] H)) (hL2 : ∀ v w : H, MemLp (cf π v w) 2 μ) (v w v' w' : H) :
    Integrable (fun g => cf π v w g * star (cf π v' w' g)) μ := by sorry
