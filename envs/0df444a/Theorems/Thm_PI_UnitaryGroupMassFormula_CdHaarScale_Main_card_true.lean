-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CdHaarScale_Main_card_true
-- name    : PI.UnitaryGroupMassFormula.CdHaarScale.Main.card_true
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:33.736806+00:00
-- url     : https://prove2.me/theorems/d94d723f-ad8c-4100-8100-af67e42e3c42
-- title:
--   Main: card true
-- statement:
--   The Main construction uses the card true property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L175-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean#L175-L186

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CdHaarScale PI.UnitaryGroupMassFormula.CdHaarScale.Main

theorem PI.UnitaryGroupMassFormula.CdHaarScale.Main.card_true {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    (Finset.univ.filter (fun i : Fin n => ε i = true)).card = P := by sorry
