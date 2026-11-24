-- Prove2me | Theorems.Thm_PI_LowUniSplit_mul_below
-- name    : PI.LowUniSplit.mul_below
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:39:25.01731+00:00
-- url     : https://prove2.me/theorems/cbf5b395-4acc-4411-9fd3-b262aa8d388d
-- title:
--   Low Uni Split: mul below
-- statement:
--   The Low Uni Split construction uses the mul below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L89-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L89-L113

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

theorem PI.LowUniSplit.mul_below {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ LTset m) (hb : b ∈ LTset m)
    {i j : Fin m} (hji : j < i) :
    (a * b) i j = a i j + b i j + ∑ k : Btw i j, a i k.1 * b k.1 j := by sorry
