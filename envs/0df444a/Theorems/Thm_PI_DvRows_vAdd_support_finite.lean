-- Prove2me | Theorems.Thm_PI_DvRows_vAdd_support_finite
-- name    : PI.DvRows.vAdd_support_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:33.040025+00:00
-- url     : https://prove2.me/theorems/d0f28df6-4e41-4293-bb5d-85a6f4091ce5
-- title:
--   Dv Rows: v Add support finite
-- statement:
--   The Dv Rows construction uses the v Add support finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean#L20-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
variable {K : Type} [Field K] [NumberField K]

theorem PI.DvRows.vAdd_support_finite (x : K) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => vAdd w x).Finite := by sorry
