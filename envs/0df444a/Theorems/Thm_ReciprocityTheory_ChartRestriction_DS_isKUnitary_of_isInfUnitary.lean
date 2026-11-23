-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_isKUnitary_of_isInfUnitary
-- name    : ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:59.133109+00:00
-- url     : https://prove2.me/theorems/1dc19cad-2bbd-475c-9ca1-94e71b191ebc
-- title:
--   DS: is KUnitary of is Inf Unitary
-- statement:
--   The DS construction uses the is KUnitary of is Inf Unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/IsKUnitaryOfIsInfUnitary.lean#L22-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.isKUnitary_of_isInfUnitary (hU : IsInfUnitary ε A) : IsKUnitary ε A := by sorry
