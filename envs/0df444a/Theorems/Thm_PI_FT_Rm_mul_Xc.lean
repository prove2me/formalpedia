-- Prove2me | Theorems.Thm_PI_FT_Rm_mul_Xc
-- name    : PI.FT.Rm_mul_Xc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:05.669847+00:00
-- url     : https://prove2.me/theorems/2435ab91-b1bf-4dc2-a6d4-0fd576844be5
-- title:
--   FT: Rm mul Xc
-- statement:
--   The FT construction uses the Rm mul Xc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L72-L74

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
variable {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
  {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}

theorem PI.FT.Rm_mul_Xc (hb : b ≠ 0) (hx : hE σ J (x 0) (x 0) = b) : Rm σ J J' B x b * Xc x = 0 := by sorry
