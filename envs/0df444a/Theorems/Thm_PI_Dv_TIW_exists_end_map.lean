-- Prove2me | Theorems.Thm_PI_Dv_TIW_exists_end_map
-- name    : PI.Dv.TIW.exists_end_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:28:04.252978+00:00
-- url     : https://prove2.me/theorems/19e4d698-18c1-4a90-b6e6-57c31dcc6fa8
-- title:
--   TIW: exists end map
-- statement:
--   The TIW construction uses the exists end map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L30-L32

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

theorem PI.Dv.TIW.exists_end_map (w u : W) (hw : w ≠ 0) : ∃ M : Module.End K W, M w = u := by sorry
