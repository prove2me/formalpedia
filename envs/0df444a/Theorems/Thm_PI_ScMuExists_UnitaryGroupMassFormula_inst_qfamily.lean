-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inst_qfamily
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.inst_qfamily
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:42.473199+00:00
-- url     : https://prove2.me/theorems/051a2806-0f14-4300-a79a-8ad22cd5ec43
-- title:
--   Unitary Group Mass Formula: inst qfamily
-- statement:
--   The Unitary Group Mass Formula construction uses the inst qfamily property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstAdapt.lean#L65-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/InstAdapt.lean#L65-L167

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAdapt
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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula

theorem PI.ScMuExists.UnitaryGroupMassFormula.inst_qfamily {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ) (hQQ : Q * Q = Q)
    (hQJ : Qᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Q) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ),
      Wᴴ * Formalism.REAL.Jm ε * W =
        diagonal (fun i => if lam i = 0 then (0 : ℂ) else if 0 < lam i then 1 else -1) ∧
      Q * W = W ∧
      (∀ x : Fin n → ℂ, Q *ᵥ x = x → ∃ y : Fin n → ℂ, (∀ i, lam i = 0 → y i = 0) ∧ x = W *ᵥ y) ∧
      Fintype.card {i // lam i ≠ 0} = Q.rank ∧
      ∃ (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℂ), W = Q * U * diagonal s := by sorry
