-- Prove2me | Theorems.Thm_PI_UnitaryCorollaryDerivatives_cD_list
-- name    : PI.UnitaryCorollaryDerivatives.cD_list
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:39:04.491342+00:00
-- url     : https://prove2.me/theorems/1699f52a-d7a3-429a-8eec-947271bf6040
-- title:
--   Unitary Corollary Derivatives: c D list
-- statement:
--   The Unitary Corollary Derivatives construction uses the c D list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStarOf.lean#L55-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStarOf.lean#L55-L74

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStarOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k j ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryCorollaryDerivatives.cD_list {ι : Type*} {Q : ℕ} {A₁ : ℝ} {O : Set (B.Mat k (j + ρ))} {E₀ : Type*}
    (F : ι → E₀ → B.Mat k (j + ρ) → E) (Pf : E₀ → ℝ → Prop) :
    ∀ l : List ι, (∀ i ∈ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ f c, Pf f c → Good k j ρ Q A₁ O (F i f) C c) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f c, Pf f c → Good k j ρ Q A₁ O (fun g => (l.map fun i => F i f g).sum) C c := by sorry
