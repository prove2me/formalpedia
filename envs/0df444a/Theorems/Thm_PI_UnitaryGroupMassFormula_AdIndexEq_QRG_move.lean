-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_move
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.QRG.move
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:55.945+00:00
-- url     : https://prove2.me/theorems/fdbf9705-7ed4-4295-b5f5-86c79de99b14
-- title:
--   QRG: move
-- statement:
--   The QRG construction uses the move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L183-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L183-L211

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.QRG.move (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (u y : Fin n → K)
    (huy : H σ J u u = H σ J y y) (ha : H σ J (u - y) (u - y) ≠ 0) :
    ∃ α : K, σ α * α = 1 ∧ Rm σ J (u - y) α *ᵥ u = y ∧
      ∀ z, H σ J (u - y) z = 0 → Rm σ J (u - y) α *ᵥ z = z := by sorry
