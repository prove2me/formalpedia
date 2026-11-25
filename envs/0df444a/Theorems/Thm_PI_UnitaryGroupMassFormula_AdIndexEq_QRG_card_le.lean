-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_card_le
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.QRG.card_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:58.726053+00:00
-- url     : https://prove2.me/theorems/211c4a18-a5c2-525f-b445-2547536e61f0
-- title:
--   QRG: card le
-- statement:
--   The QRG construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L239-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L239-L250

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)

theorem PI.UnitaryGroupMassFormula.AdIndexEq.QRG.card_le {m : ℕ} (f : Fin m → Fin n → K)
    (hf : ∀ i, H σ J (f i) (f i) ≠ 0) (ho : ∀ i j, i ≠ j → H σ J (f i) (f j) = 0) : m ≤ n := by sorry
