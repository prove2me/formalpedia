-- Prove2me | Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_pair
-- name    : PI.ScPiBuildW.Loc.LocFrame.pair
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:37:53.394839+00:00
-- url     : https://prove2.me/theorems/638eb95f-dc60-4253-b4aa-120b64fa028a
-- title:
--   Loc Frame: pair
-- statement:
--   The Loc Frame construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L140-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorFrameConstruction/LocalFramePreservesOrthogonal.lean#L140-L146

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
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)

theorem PI.ScPiBuildW.Loc.LocFrame.pair (x : Fin n → ℂ) (g : (Fin r ⊕ Fin r) ⊕ (Unit ⊕ Fin k) → ℂ) :
    hJ ε x (∑ i, g i • L.fam i) =
      (∑ a, g (.inl (.inl a)) * hJ ε x (L.e a)) + (∑ a, g (.inl (.inr a)) * hJ ε x (L.f a)) +
        (g (.inr (.inl ())) * hJ ε x L.z + ∑ c, g (.inr (.inr c)) * hJ ε x (L.w c)) := by sorry
