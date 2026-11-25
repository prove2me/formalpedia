-- Prove2me | Theorems.Thm_PI_KFinSmoothW_gv_sub_norm_le
-- name    : PI.KFinSmoothW.gv_sub_norm_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:32:50.956094+00:00
-- url     : https://prove2.me/theorems/96ef9738-3079-4e4d-bf06-1b7146b4655f
-- title:
--   KFin Smooth W: gv sub norm le
-- statement:
--   The KFin Smooth W construction uses the gv sub norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L26-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KFiniteSmoothVectors/DenseWeakVectors.lean#L26-L58

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem PI.KFinSmoothW.gv_sub_norm_le [CompleteSpace H] {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hτ : IsURepOn (UJset ε) τ)
    (Φr : Matrix (Fin n) (Fin n) ℂ → ℝ) (hΦc : Continuous Φr) (hΦ0 : ∀ x, 0 ≤ Φr x)
    (hint : Integrable (fun h : UJ ε => Φr (umat h)) (muG ε))
    (h1 : ∫ h, Φr (umat h) ∂(muG ε) = 1) (u : H) (δ : ℝ)
    (hsupp : ∀ h : UJ ε, Φr (umat h) ≠ 0 → ‖τ (umat h) u - u‖ ≤ δ) :
    ‖gv ε τ (fun x => (Φr x : ℂ)) u - u‖ ≤ δ := by sorry
