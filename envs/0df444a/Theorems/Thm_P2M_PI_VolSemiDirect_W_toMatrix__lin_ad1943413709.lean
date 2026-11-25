-- Prove2me | Theorems.Thm_P2M_PI_VolSemiDirect_W_toMatrix__lin_ad1943413709
-- name    : P2M_PI_VolSemiDirect_W_toMatrix__lin_ad1943413709
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:03:26.3+00:00
-- url     : https://prove2.me/theorems/6648162e-fe54-4f07-b30a-74d93ca11f59
-- title:
--   P2 M PI Vol Semi Direct W to Matrix  lin ad1943413709: P2 M PI Vol Semi Direct W to Matrix  lin ad1943413709
-- statement:
--   The P2 M PI Vol Semi Direct W to Matrix  lin ad1943413709 construction uses the P2 M PI Vol Semi Direct W to Matrix  lin ad1943413709 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjCont.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ProjCont.lean#L16-L23

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

theorem P2M_PI_VolSemiDirect_W_toMatrix__lin_ad1943413709 (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by sorry

alias «PI».«VolSemiDirect».«W».«toMatrix'_lin» := P2M_PI_VolSemiDirect_W_toMatrix__lin_ad1943413709
