-- Prove2me | Theorems.Thm_PI_Dv_ProjAW_mem_cutE
-- name    : PI.Dv.ProjAW.mem_cutE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:44.718818+00:00
-- url     : https://prove2.me/theorems/5f61ab18-2590-4b23-b36f-f6b2996cba0e
-- title:
--   Proj AW: mem cut E
-- statement:
--   The Proj AW construction uses the mem cut E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LengthIndex/LenAtEqZero.lean#L17-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)

theorem PI.Dv.ProjAW.mem_cutE (f : Module.End K A.V) (M : Submodule (𝓞 K) A.V) (x : A.V) :
    x ∈ cutE A f M ↔ x ∈ M ∧ x ∈ LinearMap.range f := by sorry
