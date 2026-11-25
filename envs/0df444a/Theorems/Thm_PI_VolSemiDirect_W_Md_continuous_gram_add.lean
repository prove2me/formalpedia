-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_gram_add
-- name    : PI.VolSemiDirect.W.Md.continuous_gram_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:31.511307+00:00
-- url     : https://prove2.me/theorems/be6e902c-24dd-4cb4-87ff-d18bdb2e3080
-- title:
--   Md: continuous gram add
-- statement:
--   The Md construction uses the continuous gram add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L203-L209

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

theorem PI.VolSemiDirect.W.Md.continuous_gram_add {X : Type} [TopologicalSpace X] (κ : R ⊗[F] E)
    {w : X → Fin r → Fin M → R ⊗[F] E} {c : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hc : Continuous c) :
    Continuous fun x => fun a b : Fin r => c x a b + κ * hR R σ J (w x a) (w x b) := by sorry
