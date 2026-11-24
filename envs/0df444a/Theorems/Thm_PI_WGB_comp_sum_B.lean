-- Prove2me | Theorems.Thm_PI_WGB_comp_sum_B
-- name    : PI.WGB.comp_sum_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:25.19054+00:00
-- url     : https://prove2.me/theorems/65db50e1-e031-46db-bd62-a8b23554edb3
-- title:
--   WGB: comp sum B
-- statement:
--   The WGB construction uses the comp sum B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L93-L103

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

theorem PI.WGB.comp_sum_B {σ M : Type*} [AddCommMonoid M] [DecidableEq M] (w : σ → M) (f : MvPolynomial σ ℂ)
    (F : Finset M) (hF : ∀ e ∈ f.support, Finsupp.weight w e ∈ F) :
    ∑ m ∈ F, weightedHomogeneousComponent w m f = f := by sorry
