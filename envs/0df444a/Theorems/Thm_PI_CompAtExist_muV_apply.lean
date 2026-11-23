-- Prove2me | Theorems.Thm_PI_CompAtExist_muV_apply
-- name    : PI.CompAtExist.muV_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:07.349531+00:00
-- url     : https://prove2.me/theorems/b60132b3-42ac-4c9e-bfb1-71b62bf78e6f
-- title:
--   Comp At Exist: mu V apply
-- statement:
--   The Comp At Exist construction uses the mu V apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L93-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionExistence/LeOneIffOfMulEqOne.lean#L93-L93

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionExistence_LeOneIffOfMulEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CompAtExist
open NumberField IsDedekindDomain ReciprocityTheory.Aut
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem PI.CompAtExist.muV_apply (s : SplitPlace L) (k : L) : muV s k = Valued.v (s.i k) := by sorry
