-- Prove2me | Theorems.Thm_PI_LowUniSplit_first_factor_mem_lower_triangular
-- name    : PI.LowUniSplit.first_factor_mem_lower_triangular
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:34.073738+00:00
-- url     : https://prove2.me/theorems/85702bf9-7ede-4598-bb60-8ea9498233cb
-- title:
--   Low Uni Split: first factor mem lower triangular
-- statement:
--   The Low Uni Split construction uses the first factor mem lower triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L138-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L138-L140

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

theorem PI.LowUniSplit.first_factor_mem_lower_triangular : fac1 S l ∈ LTset m := by sorry
