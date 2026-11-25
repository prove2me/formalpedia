-- Prove2me | Theorems.Thm_PI_LowUniSplit_mem_Lstg_iff
-- name    : PI.LowUniSplit.mem_Lstg_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:48.580877+00:00
-- url     : https://prove2.me/theorems/cebc8751-4eef-44f1-9bc7-ea29a0d023cc
-- title:
--   Low Uni Split: mem Lstg iff
-- statement:
--   The Low Uni Split construction uses the mem Lstg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerUnipotentSplit/SecondFactorMemLowerTriangular.lean#L53-L67

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

theorem PI.LowUniSplit.mem_Lstg_iff (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ LTset m) :
    l ∈ Lstg (monoP w d) ↔ ∀ i j, w.symm j < w.symm i → l i j = 0 := by sorry
