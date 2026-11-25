-- Prove2me | Theorems.Thm_PI_Dv_RK_mul_eS
-- name    : PI.Dv.RK.mul_eS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:59.66051+00:00
-- url     : https://prove2.me/theorems/f8462a0e-2608-48c3-98ec-bd9bed794686
-- title:
--   RK: mul e S
-- statement:
--   The RK construction uses the mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/AsAlgApply.lean#L12-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply
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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.RK.mul_eS (T : GoodSet K G) (s : T.S) (z : MonoidAlgebra K G) :
    z * eS T s = ∑ g : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (T.tau s g⁻¹ * (T.tau s).asAlgebraHom z)) •
        MonoidAlgebra.of K G g := by sorry
