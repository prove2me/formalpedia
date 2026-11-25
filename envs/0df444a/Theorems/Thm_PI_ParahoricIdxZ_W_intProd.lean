-- Prove2me | Theorems.Thm_PI_ParahoricIdxZ_W_intProd
-- name    : PI.ParahoricIdxZ.W.intProd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:52.396976+00:00
-- url     : https://prove2.me/theorems/23080763-a51c-46bf-945c-5185e755c408
-- title:
--   W: int Prod
-- statement:
--   The W construction uses the int Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ParahoricIndexCount/ThetaInjective.lean#L58-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
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
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

theorem PI.ParahoricIdxZ.W.intProd {l m n : Type} [Fintype m] {X : Matrix l m F} {Y : Matrix m n F}
    (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O) : ∀ i j, (X * Y) i j ∈ O := by sorry
