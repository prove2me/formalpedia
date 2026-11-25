-- Prove2me | Theorems.Thm_PI_FT_formulaB
-- name    : PI.FT.formulaB
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:08.895705+00:00
-- url     : https://prove2.me/theorems/fbe512e9-db27-4bca-84f9-73e31e0c87a0
-- title:
--   FT: formula B
-- statement:
--   The FT construction uses the formula B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L111-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameTransport/MemHFinInIff.lean#L111-L128

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

theorem PI.FT.formulaB {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {J' : Matrix (Fin M) (Fin M) E}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {x : Fin 1 → Fin (M + 1) → E} {b : E}
    (hdec : Xc x * qm σ J x b + B * Rm σ J J' B x b = 1)
    (G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E)) (G' : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hX : G * (Xc x).map (inclR (F := F) (E := E) R) = (Xc x).map (inclR (F := F) (E := E) R))
    (h : G * B.map (inclR (F := F) (E := E) R) = B.map (inclR (F := F) (E := E) R) * G') :
    G = (Xc x).map (inclR (F := F) (E := E) R) * (qm σ J x b).map (inclR (F := F) (E := E) R) +
      B.map (inclR (F := F) (E := E) R) * G' * (Rm σ J J' B x b).map (inclR (F := F) (E := E) R) := by sorry
