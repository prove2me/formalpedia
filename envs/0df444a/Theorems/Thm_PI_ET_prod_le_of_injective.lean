-- Prove2me | Theorems.Thm_PI_ET_prod_le_of_injective
-- name    : PI.ET.prod_le_of_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:33.990708+00:00
-- url     : https://prove2.me/theorems/1694d3bb-b44c-5291-802e-7d395c21ffcd
-- title:
--   ET: prod le of injective
-- statement:
--   The ET construction uses the prod le of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/ProdLeOfInjective.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/ProdLeOfInjective.lean#L65-L89

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

theorem PI.ET.prod_le_of_injective {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 ≤ p i) (f : Fin k → Fin n) (hf : Function.Injective f) :
    ∏ i, p (f i) ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by sorry
