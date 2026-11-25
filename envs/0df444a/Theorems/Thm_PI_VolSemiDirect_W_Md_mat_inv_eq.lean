-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_Md_mat_inv_eq
-- name    : PI.VolSemiDirect.W.Md.mat_inv_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:08.619721+00:00
-- url     : https://prove2.me/theorems/0ae1b51d-ad15-4fcb-8df2-9878b7b239f3
-- title:
--   Md: mat inv eq
-- statement:
--   The Md construction uses the mat inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L118-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModTop.lean#L118-L145

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem PI.VolSemiDirect.W.Md.mat_inv_eq (hJ : IsHermND σ J) (g : HA R σ J) :
    ((HA.mat R σ J g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J⁻¹).map (inclR (F := F) R) *
        Formalism.UG.cT (sigR R σ) ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) :
          Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J := by sorry
