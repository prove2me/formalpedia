-- Prove2me | Theorems.Thm_PI_LowUniSplit_xs_eq
-- name    : PI.LowUniSplit.xs_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:33.216149+00:00
-- url     : https://prove2.me/theorems/bbc9f107-b136-424a-9002-9556253a2fa1
-- title:
--   Low Uni Split: xs eq
-- statement:
--   The Low Uni Split construction uses the xs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L128-L130

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
variable (S : Fin m → Fin m → Prop) [DecidableRel S] (l : Matrix (Fin m) (Fin m) ℂ)

theorem PI.LowUniSplit.xs_eq (i j : Fin m) : xs S l i j = l i j - ∑ k : Btw i j,
    (if S i k.1 then xs S l i k.1 else 0) * (if S k.1 j then 0 else xs S l k.1 j) := by sorry
