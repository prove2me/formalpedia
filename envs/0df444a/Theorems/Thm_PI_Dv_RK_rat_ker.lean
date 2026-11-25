-- Prove2me | Theorems.Thm_PI_Dv_RK_rat_ker
-- name    : PI.Dv.RK.rat_ker
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:27:56.369959+00:00
-- url     : https://prove2.me/theorems/d1201e83-5e4c-4b02-86ec-b1188eee7d2d
-- title:
--   RK: rat ker
-- statement:
--   The RK construction uses the rat ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean#L87-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalKernels/OfMulEps.lean#L87-L126

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

theorem PI.Dv.RK.rat_ker (P0 : Pair K G)
    (hF : eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P0 * b})
    (hR : M.IsRat (LinearMap.ker M.io ⊓ eigP σ P0 M.rho)) : M.IsRat (LinearMap.ker M.io) := by sorry
