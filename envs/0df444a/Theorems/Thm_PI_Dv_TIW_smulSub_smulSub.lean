-- Prove2me | Theorems.Thm_PI_Dv_TIW_smulSub_smulSub
-- name    : PI.Dv.TIW.smulSub_smulSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:07.155468+00:00
-- url     : https://prove2.me/theorems/47b606ba-303d-41a6-b409-ad51d7685d46
-- title:
--   TIW: smul Sub smul Sub
-- statement:
--   The TIW construction uses the smul Sub smul Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean#L67-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.TIW.smulSub_smulSub (d e : K) (L : Submodule (𝓞 K) V) : smulSub d (smulSub e L) = smulSub (d * e) L := by sorry
