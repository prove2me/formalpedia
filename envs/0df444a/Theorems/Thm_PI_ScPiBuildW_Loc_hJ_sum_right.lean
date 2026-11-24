-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_hJ_sum_right
-- name    : PI.ScPiBuildW.Loc.hJ_sum_right
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:54:26.958895+00:00
-- url     : https://prove2.me/theorems/a472d696-0522-4b08-8f44-153165976042
-- title:
--   Loc: h J sum right
-- statement:
--   The Loc construction uses the h J sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L41-L46

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

theorem PI.ScPiBuildW.Loc.hJ_sum_right {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (u : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * hJ ε x (u i) := by sorry
