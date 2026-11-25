-- Prove2me | Theorems.Thm_PI_FT_cT_map_incl
-- name    : PI.FT.cT_map_incl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:19.889799+00:00
-- url     : https://prove2.me/theorems/16676301-4674-4c1a-b3b7-627f620b2265
-- title:
--   FT: c T map incl
-- statement:
--   The FT construction uses the c T map incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L146-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L146-L150

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
variable (R : Type) [CommRing R] [Algebra F R]

theorem PI.FT.cT_map_incl {m n : ℕ} (a : Matrix (Fin m) (Fin n) E) :
    (Formalism.UG.cT (σ : E →+* E) a).map (inclR (F := F) (E := E) R) =
      Formalism.UG.cT (sigR R σ) (a.map (inclR (F := F) (E := E) R)) := by sorry
