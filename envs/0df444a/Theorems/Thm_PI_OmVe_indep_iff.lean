-- Prove2me | Theorems.Thm_PI_OmVe_indep_iff
-- name    : PI.OmVe.indep_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:15:37.474216+00:00
-- url     : https://prove2.me/theorems/9d59c76c-7b08-49d8-a893-e37acd2c3326
-- title:
--   Om Ve: indep iff
-- statement:
--   The Om Ve construction uses the indep iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L56-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/SingleMulVec.lean#L56-L98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_SingleMulVec
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

theorem PI.OmVe.indep_iff {a : ℕ} {T : Matrix (Fin a) (Fin a) K} (i₀ : Fin a) (hc : ∀ j, T j i₀ = 0)
    (hu : IsUnit (T + Matrix.single i₀ i₀ 1).det) (X : Fin a → Fin M → K) (hX : ffGram σ J X = T) :
    LinearIndependent K X ↔ ∀ c : K, c • X i₀ = 0 → c = 0 := by sorry
