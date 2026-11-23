-- Prove2me | Theorems.Thm_PI_Dv_TIW_exists_dual_one
-- name    : PI.Dv.TIW.exists_dual_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:46.708324+00:00
-- url     : https://prove2.me/theorems/66ec098e-2421-473f-b7c1-f0615c9de472
-- title:
--   TIW: exists dual one
-- statement:
--   The TIW construction uses the exists dual one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L12-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem PI.Dv.TIW.exists_dual_one (w : W) (hw : w ≠ 0) : ∃ φ : Module.Dual K W, φ w = 1 := by sorry
