-- Prove2me | Theorems.Thm_PI_EF_Lent_two_ne_zero
-- name    : PI.EF.Lent_two_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:13.648587+00:00
-- url     : https://prove2.me/theorems/68ff291c-2a00-441b-8bfb-2b671b52db3a
-- title:
--   EF: Lent two ne zero
-- statement:
--   The EF construction uses the Lent two ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructC.lean#L44-L51

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

theorem PI.EF.Lent_two_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 2 ≠ 0 := by sorry
