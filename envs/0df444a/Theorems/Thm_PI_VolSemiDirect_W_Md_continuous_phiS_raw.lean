-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_phiS_raw
-- name    : PI.VolSemiDirect.W.Md.continuous_phiS_raw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:19.781572+00:00
-- url     : https://prove2.me/theorems/853d53c0-dc21-47d5-8586-d9c2350500e3
-- title:
--   Md: continuous phi S raw
-- statement:
--   The Md construction uses the continuous phi S raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L187-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L187-L193

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
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)] (σ : E →ₐ[F] E)
  {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)

theorem PI.VolSemiDirect.W.Md.continuous_phiS_raw :
    Continuous fun n : FrameUnipotentSubgroup R σ J P => fun a b : Fin r =>
      hR R σ J (ratV (F := F) R (P.f a)) (lin R σ J (n : HA R σ J) (ratV (F := F) R (P.f b))) := by sorry
