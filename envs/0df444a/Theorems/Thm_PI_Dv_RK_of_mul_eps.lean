-- Prove2me | Theorems.Thm_PI_Dv_RK_of_mul_eps
-- name    : PI.Dv.RK.of_mul_eps
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:03.537925+00:00
-- url     : https://prove2.me/theorems/e297f787-f15a-4b93-aa6d-0f8b62150d81
-- title:
--   RK: of mul eps
-- statement:
--   The RK construction uses the of mul eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean#L18-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}

theorem PI.Dv.RK.of_mul_eps (P : Pair K G) (h : P.H) :
    MonoidAlgebra.of K G (h : G) * eps P = ((P.chi h : Kˣ) : K) • eps P := by sorry
