-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_L_apply
-- name    : PI.VolSemiDirect.W.Md.continuous_L_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:08.829796+00:00
-- url     : https://prove2.me/theorems/e621ac03-2468-496e-b240-02a49a5e2e0e
-- title:
--   Md: continuous L apply
-- statement:
--   The Md construction uses the continuous L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L67-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L67-L99

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

theorem PI.VolSemiDirect.W.Md.continuous_L_apply {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => (datR R σ J P T).L (w x) (s x) v := by sorry
