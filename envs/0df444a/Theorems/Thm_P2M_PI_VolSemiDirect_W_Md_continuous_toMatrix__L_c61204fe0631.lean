-- Prove2me | Theorems.Thm_P2M_PI_VolSemiDirect_W_Md_continuous_toMatrix__L_c61204fe0631
-- name    : P2M_PI_VolSemiDirect_W_Md_continuous_toMatrix__L_c61204fe0631
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:44:42.886257+00:00
-- url     : https://prove2.me/theorems/a1b69a8a-bafc-46d5-b345-d4b62e459953
-- title:
--   P2 M PI Vol Semi Direct W Md continuous to Matrix  L c61204fe0631: P2 M PI Vol Semi Direct W Md continuous to Matrix  L c61204fe0631
-- statement:
--   The P2 M PI Vol Semi Direct W Md continuous to Matrix  L c61204fe0631 construction uses the P2 M PI Vol Semi Direct W Md continuous to Matrix  L c61204fe0631 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L101-L109

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

theorem P2M_PI_VolSemiDirect_W_Md_continuous_toMatrix__L_c61204fe0631 {X : Type} [TopologicalSpace X]
    {w : X → Fin r → Fin M → R ⊗[F] E} {s : X → Fin r → Fin r → R ⊗[F] E}
    (hw : Continuous w) (hs : Continuous s) :
    Continuous fun x => LinearMap.toMatrix' ((datR R σ J P T).L (w x) (s x)) := by sorry

alias «PI».«VolSemiDirect».«W».«Md».«continuous_toMatrix'_L» := P2M_PI_VolSemiDirect_W_Md_continuous_toMatrix__L_c61204fe0631
