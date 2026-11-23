-- Prove2me | Theorems.Thm_PI_WGB_rowAct_comp_apply
-- name    : PI.WGB.rowAct_comp_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:29.170863+00:00
-- url     : https://prove2.me/theorems/50308ba0-3bff-479c-84b0-199c650042ad
-- title:
--   WGB: row Act comp apply
-- statement:
--   The WGB construction uses the row Act comp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/AevalScaleMonomial.lean#L21-L23

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

theorem PI.WGB.rowAct_comp_apply {R : Type} [CommRing R] {r c : ℕ} (A B : Matrix (Fin r) (Fin r) R)
    (p : MvPolynomial (Fin r × Fin c) R) : rowAct R B (rowAct R A p) = rowAct R (A * B) p := by sorry
