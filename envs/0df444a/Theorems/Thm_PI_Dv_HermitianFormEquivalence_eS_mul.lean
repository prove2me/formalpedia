-- Prove2me | Theorems.Thm_PI_Dv_HermitianFormEquivalence_eS_mul
-- name    : PI.Dv.HermitianFormEquivalence.eS_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:19.606846+00:00
-- url     : https://prove2.me/theorems/4c9a641f-0f5f-4bd2-a2cf-fc8f2c3dadb5
-- title:
--   Hermitian Form Equivalence: e S mul
-- statement:
--   The Hermitian Form Equivalence construction uses the e S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/ExistsSumEqOne.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceFormEquality/ExistsSumEqOne.lean#L30-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_ExistsSumEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.HermitianFormEquivalence
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.HermitianFormEquivalence.eS_mul (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phi T s ((T.tau s).asAlgebraHom a) := by sorry
