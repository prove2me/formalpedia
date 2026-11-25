-- Prove2me | Theorems.Thm_PI_FT_formulaA
-- name    : PI.FT.formulaA
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:23.492142+00:00
-- url     : https://prove2.me/theorems/9d135989-5b46-4c1f-b413-b4f21c4ecd65
-- title:
--   FT: formula A
-- statement:
--   The FT construction uses the formula A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L102-L109

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

theorem PI.FT.formulaA {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} (hLB : Lm σ J J' B * B = 1)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) (G' : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (h : G * B.map (inclR (F := F) (E := E) R) = B.map (inclR (F := F) (E := E) R) * G') :
    G' = (Lm σ J J' B).map (inclR (F := F) (E := E) R) * G * B.map (inclR (F := F) (E := E) R) := by sorry
