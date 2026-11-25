-- Prove2me | Theorems.Thm_PI_WGB_sep_mem_B
-- name    : PI.WGB.sep_mem_B
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:45:37.93662+00:00
-- url     : https://prove2.me/theorems/f7403d0b-e97a-4c32-87e9-ca257653ef12
-- title:
--   WGB: sep mem B
-- statement:
--   The WGB construction uses the sep mem B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L114-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L114-L153

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

theorem PI.WGB.sep_mem_B {ι T V : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (C : T → Module.End ℂ V) (p : ι → T → ℂ) (P : Submodule ℂ V) (hP : ∀ t, ∀ x ∈ P, C t x ∈ P)
    (hsep : ∀ i j, i ≠ j → ∃ t, p i t ≠ p j t) :
    ∀ (F : Finset ι) (y : ι → V), (∀ i ∈ F, ∀ t, C t (y i) = p i t • y i) → ∑ i ∈ F, y i ∈ P →
      ∀ i ∈ F, y i ∈ P := by sorry
