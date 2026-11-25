-- Prove2me | Theorems.Thm_PI_WSF_evA_diag
-- name    : PI.WSF.evA_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:56:49.420117+00:00
-- url     : https://prove2.me/theorems/c5076e13-d2c1-5a09-85ca-99322e0c3f9f
-- title:
--   WSF: ev A diag
-- statement:
--   The WSF construction uses the ev A diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SchurOrthogonality/ConstructionA.lean#L90-L103

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_InstMeasurableSpaceMat
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurOrthogonality_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WSF
open Formalism.BasicNotions MvPolynomial MeasureTheory

theorem PI.WSF.evA_diag {N : ℕ} (d : Fin N × Fin N →₀ ℕ)
    (h : (∏ v ∈ d.support, ((1 : Matrix (Fin N) (Fin N) ℂ) v.1 v.2) ^ d v) ≠ 0) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.rowW N N) d = Finsupp.weight (Formalism.GradedWeylDivisibility.colW N N) d := by sorry
