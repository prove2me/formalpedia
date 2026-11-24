-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_QRG_main
-- name    : PI.UnitaryGroupMassFormula.AdIndexEq.QRG.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:43.912658+00:00
-- url     : https://prove2.me/theorems/8a6cb7f2-0f1f-47f0-a38f-2cd08542f626
-- title:
--   QRG: main
-- statement:
--   The QRG construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L252-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/InertGen.lean#L252-L453

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

theorem PI.UnitaryGroupMassFormula.AdIndexEq.QRG.main (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (hdet : J.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (d : ℕ) : ∀ (k : ℕ) (e : Fin k → Fin n → K), n - k = d → (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∀ g : UJ σ J, (∀ i, gm σ J g *ᵥ e i = e i) → g ∈ S σ J := by sorry
