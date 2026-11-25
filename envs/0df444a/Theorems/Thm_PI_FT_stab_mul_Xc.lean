-- Prove2me | Theorems.Thm_PI_FT_stab_mul_Xc
-- name    : PI.FT.stab_mul_Xc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:58.413965+00:00
-- url     : https://prove2.me/theorems/35ef06dc-910f-42f7-aaac-98be243d46a3
-- title:
--   FT: stab mul Xc
-- statement:
--   The FT construction uses the stab mul Xc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L130-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L130-L144

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

theorem PI.FT.stab_mul_Xc {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    (g : Hstab R σ J x) :
    ((HA.mat R σ J (g : HA R σ J) : GL (Fin (M + 1)) (R ⊗[F] E)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) * (Xc x).map (inclR (F := F) (E := E) R) =
      (Xc x).map (inclR (F := F) (E := E) R) := by sorry
