-- Prove2me | Theorems.Thm_PI_FT_Lm_mul
-- name    : PI.FT.Lm_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:45.250197+00:00
-- url     : https://prove2.me/theorems/23100832-5558-431a-8bf6-981d34beddb0
-- title:
--   FT: Lm mul
-- statement:
--   The FT construction uses the Lm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L19-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}

theorem PI.FT.Lm_mul {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hJ' : J' = Formalism.UG.cT (σ : E →+* E) B * J * B)
    (hd : J'.det ≠ 0) : Lm σ J J' B * B = 1 := by sorry
