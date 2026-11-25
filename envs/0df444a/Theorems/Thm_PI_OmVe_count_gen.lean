-- Prove2me | Theorems.Thm_PI_OmVe_count_gen
-- name    : PI.OmVe.count_gen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:29:03.578407+00:00
-- url     : https://prove2.me/theorems/11085c42-b615-461f-9bb3-c564148c83d6
-- title:
--   Om Ve: count gen
-- statement:
--   The Om Ve construction uses the count gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/CountGen.lean#L14-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/CountGen.lean#L14-L96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CardAndAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

theorem PI.OmVe.count_gen [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (haM : a' ≤ M)
    {k : Type} [Finite k] [Zero k] (ι : k → K) (hι : Function.Injective ι) (hι0 : ι 0 = 0)
    (hrange : ∀ x : Fin M → K, ∃ c, ffH σ J x x = ι c) (N D : ℕ)
    (hN : ∀ c, c ≠ 0 → Nat.card {X : Fin (a' + 1) → Fin M → K //
      ffGram σ J X = T + Matrix.single i₀ i₀ (ι c)} = N)
    (hD : ∀ Y : Fin a' → Fin M → K, ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove →
      Nat.card {x : Fin M → K // (∀ j, ffH σ J (Y j) x = 0) ∧ ffH σ J x x = 0 ∧
        ¬ ∀ c : K, c • x = 0 → c = 0} = D) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T ∧ LinearIndependent K X} +
      Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} * D +
      (Nat.card k - 1) * N =
    Nat.card {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove} *
      Nat.card K ^ (M - a') := by sorry
