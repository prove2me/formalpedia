-- Prove2me | Theorems.Thm_PI_LowUniSplit_monoInv_mul
-- name    : PI.LowUniSplit.monoInv_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:52.775856+00:00
-- url     : https://prove2.me/theorems/d824a776-1476-5479-a999-4629d15e0d18
-- title:
--   Low Uni Split: mono Inv mul
-- statement:
--   The Low Uni Split construction uses the mono Inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L16-L24

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.LowUniSplit
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}

theorem PI.LowUniSplit.monoInv_mul (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    monoInv w d * monoP w d = 1 := by sorry
