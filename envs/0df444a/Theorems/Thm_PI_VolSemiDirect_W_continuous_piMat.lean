-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_continuous_piMat
-- name    : PI.VolSemiDirect.W.continuous_piMat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:41.098134+00:00
-- url     : https://prove2.me/theorems/dc6447ba-11ea-4251-a231-dd4a18943f97
-- title:
--   W: continuous pi Mat
-- statement:
--   The W construction uses the continuous pi Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjCont.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjCont.lean#L42-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem PI.VolSemiDirect.W.continuous_piMat [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by sorry
