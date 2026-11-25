-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_piMat_eq
-- name    : PI.VolSemiDirect.W.piMat_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:17.901147+00:00
-- url     : https://prove2.me/theorems/d0e6376b-867f-5c6a-b9fb-a0fdc48257df
-- title:
--   W: pi Mat eq
-- statement:
--   The W construction uses the pi Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjCont.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjCont.lean#L25-L30

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

theorem PI.VolSemiDirect.W.piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by sorry
