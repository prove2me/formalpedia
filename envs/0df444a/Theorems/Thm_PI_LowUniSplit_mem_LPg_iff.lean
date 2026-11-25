-- Prove2me | Theorems.Thm_PI_LowUniSplit_mem_LPg_iff
-- name    : PI.LowUniSplit.mem_LPg_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:51.781797+00:00
-- url     : https://prove2.me/theorems/da22c1a0-c597-46bd-8018-681b81a8f3ed
-- title:
--   Low Uni Split: mem LPg iff
-- statement:
--   The Low Uni Split construction uses the mem LPg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L37-L51

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

theorem PI.LowUniSplit.mem_LPg_iff (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ LTset m) :
    l ∈ LPg (monoP w d) ↔ ∀ i j, w.symm i < w.symm j → l i j = 0 := by sorry
