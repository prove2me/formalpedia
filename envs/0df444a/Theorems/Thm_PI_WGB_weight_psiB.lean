-- Prove2me | Theorems.Thm_PI_WGB_weight_psiB
-- name    : PI.WGB.weight_psiB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:21.36231+00:00
-- url     : https://prove2.me/theorems/ed881291-d87e-4860-965c-559da9f59274
-- title:
--   WGB: weight psi B
-- statement:
--   The WGB construction uses the weight psi B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/RowActDiagMonomial.lean#L30-L34

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

theorem PI.WGB.weight_psiB (n N : ℕ) (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e = PsiB n (Finsupp.weight (wnB n N) e) := by sorry
