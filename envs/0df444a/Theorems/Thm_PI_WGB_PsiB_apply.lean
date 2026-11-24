-- Prove2me | Theorems.Thm_PI_WGB_PsiB_apply
-- name    : PI.WGB.PsiB_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:52.730111+00:00
-- url     : https://prove2.me/theorems/81110a47-009c-415a-bf0c-36bf84b29cd4
-- title:
--   WGB: Psi B apply
-- statement:
--   The WGB construction uses the Psi B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L21-L21

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

theorem PI.WGB.PsiB_apply (n : ℕ) (m : Fin n → ℕ) : PsiB n m = ∑ j, (n - j.1) * m j := by sorry
