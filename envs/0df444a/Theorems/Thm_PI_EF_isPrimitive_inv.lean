-- Prove2me | Theorems.Thm_PI_EF_isPrimitive_inv
-- name    : PI.EF.isPrimitive_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:07.024867+00:00
-- url     : https://prove2.me/theorems/fdb25e16-e9c7-4953-8c0f-47031ecfe41c
-- title:
--   EF: is Primitive inv
-- statement:
--   The EF construction uses the is Primitive inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LStructB.lean#L25-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructB
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
variable {N : ℕ}

theorem PI.EF.isPrimitive_inv {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by sorry
