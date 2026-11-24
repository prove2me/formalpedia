-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_nsmul_relIdx_mem
-- name    : PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:44:45.682732+00:00
-- url     : https://prove2.me/theorems/7e5b70f4-f61e-4d8e-a86b-32ceca390897
-- title:
--   Unit Det Root: nsmul rel Idx mem
-- statement:
--   The Unit Det Root construction uses the nsmul rel Idx mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/NsmulRelIdxMem.lean#L85-L89

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI

theorem PI.UnitaryGroupMassFormula.UnitDetRoot.nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (H K : AddSubgroup V) {x : V} (hx : x ∈ K) :
    (H.relIndex K) • x ∈ H := by sorry
