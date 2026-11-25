-- Prove2me | Theorems.Thm_PI_FT_cont_mul_const
-- name    : PI.FT.cont_mul_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:29.145062+00:00
-- url     : https://prove2.me/theorems/0b038fdf-fb71-43db-916d-8d19a6ada8f2
-- title:
--   FT: cont mul const
-- statement:
--   The FT construction uses the cont mul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/InstIsModTopTens.lean#L36-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem PI.FT.cont_mul_const (c d : R ⊗[F] E) : Continuous (fun a : R ⊗[F] E => c * a * d) := by sorry
