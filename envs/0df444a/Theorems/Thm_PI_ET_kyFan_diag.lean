-- Prove2me | Theorems.Thm_PI_ET_kyFan_diag
-- name    : PI.ET.kyFan_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:28.374058+00:00
-- url     : https://prove2.me/theorems/e4eccf50-8058-5b31-a96e-48b4e253d065
-- title:
--   ET: ky Fan diag
-- statement:
--   The ET construction uses the ky Fan diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/ProdLeOfInjective.lean#L91-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/ProdLeOfInjective.lean#L91-L133

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET

theorem PI.ET.kyFan_diag {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 < p i) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by sorry
