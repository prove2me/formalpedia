-- Prove2me | Theorems.Thm_PI_Dv_TIW_entry_bound
-- name    : PI.Dv.TIW.entry_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:09.435156+00:00
-- url     : https://prove2.me/theorems/6c9deb1a-087a-4df8-b408-259ec5b2899a
-- title:
--   TIW: entry bound
-- statement:
--   The TIW construction uses the entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/GroupDataExists.lean#L35-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/GroupDataExists.lean#L35-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GroupDataExists
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
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.TIW.entry_bound (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (g' g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G g' * (epsS P * MonoidAlgebra.of K G g))))‖ ≤
      ((Fintype.card G : ℕ) : ℝ) ^ 3 := by sorry
