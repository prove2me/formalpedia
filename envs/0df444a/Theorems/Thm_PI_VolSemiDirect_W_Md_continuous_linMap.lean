-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_linMap
-- name    : PI.VolSemiDirect.W.Md.continuous_linMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:04.511686+00:00
-- url     : https://prove2.me/theorems/3c6f45bd-870b-4cdb-9cb2-a9de6a2eb79a
-- title:
--   Md: continuous lin Map
-- statement:
--   The Md construction uses the continuous lin Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L44-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Md
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable [IsTopologicalRing (R ⊗[F] E)]

theorem PI.VolSemiDirect.W.Md.continuous_linMap {X : Type} [TopologicalSpace X]
    (f : (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin M → R ⊗[F] E)) {v : X → Fin M → R ⊗[F] E}
    (hv : Continuous v) : Continuous fun x => f (v x) := by sorry
