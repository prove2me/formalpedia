-- Prove2me | Theorems.Thm_PI_WGB_graded_B
-- name    : PI.WGB.graded_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:02.981819+00:00
-- url     : https://prove2.me/theorems/0a30b2f8-42af-4829-8a33-64785b0dc8eb
-- title:
--   WGB: graded B
-- statement:
--   The WGB construction uses the graded B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L199-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L199-L236

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

theorem PI.WGB.graded_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ W) (m : Fin n → ℕ) :
    weightedHomogeneousComponent (wnB n N) m f ∈ W := by sorry
