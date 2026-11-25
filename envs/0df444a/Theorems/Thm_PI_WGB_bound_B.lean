-- Prove2me | Theorems.Thm_PI_WGB_bound_B
-- name    : PI.WGB.bound_B
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:49.464188+00:00
-- url     : https://prove2.me/theorems/f9c5c97d-a716-424d-accb-5cbe9232daac
-- title:
--   WGB: bound B
-- statement:
--   The WGB construction uses the bound B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/DetPowUnitriB.lean#L160-L168

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
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

theorem PI.WGB.bound_B {n N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) (hg : g ∈ nablaSq ℂ N lam)
    (hg0 : g ≠ 0) (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) :
    PsiB n m ≤ n * ∑ s, lam.natW s := by sorry
