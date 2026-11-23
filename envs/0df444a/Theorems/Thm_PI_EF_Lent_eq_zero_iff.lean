-- Prove2me | Theorems.Thm_PI_EF_Lent_eq_zero_iff
-- name    : PI.EF.Lent_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:05.963083+00:00
-- url     : https://prove2.me/theorems/dff0e179-3d2f-4560-b843-3895d68ee776
-- title:
--   EF: Lent eq zero iff
-- statement:
--   The EF construction uses the Lent eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L61-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.Lent_eq_zero_iff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = 0 ↔ LFunction χ s = 0 := by sorry
