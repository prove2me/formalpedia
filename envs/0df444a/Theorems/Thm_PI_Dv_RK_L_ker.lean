-- Prove2me | Theorems.Thm_PI_Dv_RK_L_ker
-- name    : PI.Dv.RK.L_ker
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:57.568787+00:00
-- url     : https://prove2.me/theorems/a58410f9-b26f-4dfc-925b-5b581e7eb179
-- title:
--   RK: L ker
-- statement:
--   The RK construction uses the L ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean#L64-L71

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
variable (M : GMap K σ G T EE ρE)

theorem PI.Dv.RK.L_ker (z : MonoidAlgebra K G) {v : M.V} (hv : v ∈ LinearMap.ker M.io) :
    L M z v ∈ LinearMap.ker M.io := by sorry
