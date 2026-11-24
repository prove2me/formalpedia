-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_hJ_conj
-- name    : PI.ScPiBuildW.Loc.hJ_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:12.996583+00:00
-- url     : https://prove2.me/theorems/3c1b7391-d91a-47cd-a153-28b9f8eacf27
-- title:
--   Loc: h J conj
-- statement:
--   The Loc construction uses the h J conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L48-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
variable {n : ℕ} (ε : Fin n → Bool)

theorem PI.ScPiBuildW.Loc.hJ_conj (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by sorry
