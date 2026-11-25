-- Prove2me | Theorems.Thm_PI_WGB_rowAct_diag_homog
-- name    : PI.WGB.rowAct_diag_homog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:14.1788+00:00
-- url     : https://prove2.me/theorems/ada9b375-0f36-4374-a860-d18dad0cae45
-- title:
--   WGB: row Act diag homog
-- statement:
--   The WGB construction uses the row Act diag homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L84-L91

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
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
open Formalism.BasicNotions MvPolynomial

theorem PI.WGB.rowAct_diag_homog {n N : ℕ} (t : Fin n → ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.diagonal (dB n N t)) g = chiB t m • g := by sorry
