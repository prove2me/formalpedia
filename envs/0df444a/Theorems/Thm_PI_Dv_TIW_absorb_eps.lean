-- Prove2me | Theorems.Thm_PI_Dv_TIW_absorb_eps
-- name    : PI.Dv.TIW.absorb_eps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:53.420539+00:00
-- url     : https://prove2.me/theorems/b41852d7-ba2b-4216-a57f-212139a4285b
-- title:
--   TIW: absorb eps
-- statement:
--   The TIW construction uses the absorb eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/TraceMemOfIntR.lean#L51-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
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
open PI.Dv NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.TIW.absorb_eps (T : GoodSet K G) (s : T.S) (Q R : Pair K G) (z : MonoidAlgebra K G) :
    eps Q * eS T s * (epsS Q * z) * (eps R * eS T s) = epsS Q * z * (eps R * eS T s) := by sorry
