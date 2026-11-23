-- Prove2me | Theorems.Thm_PI_WGB_rowAct_one_apply
-- name    : PI.WGB.rowAct_one_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:55.110802+00:00
-- url     : https://prove2.me/theorems/c7a5afe1-ee1e-4f3f-b628-65076bf53fa8
-- title:
--   WGB: row Act one apply
-- statement:
--   The WGB construction uses the row Act one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L25-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

theorem PI.WGB.rowAct_one_apply {R : Type} [CommRing R] {r c : ℕ} (p : MvPolynomial (Fin r × Fin c) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) p = p := by sorry
