-- Prove2me | Theorems.Thm_P2M_PI_LevelKSplit_W_SemiA_toMatrix__lin_81c9c19a7389
-- name    : P2M_PI_LevelKSplit_W_SemiA_toMatrix__lin_81c9c19a7389
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:12.442544+00:00
-- url     : https://prove2.me/theorems/ec2db1f4-38b3-55bb-967b-0a9551e64493
-- title:
--   P2 M PI Level KSplit W Semi A to Matrix  lin 81c9c19a7389: P2 M PI Level KSplit W Semi A to Matrix  lin 81c9c19a7389
-- statement:
--   The P2 M PI Level KSplit W Semi A to Matrix  lin 81c9c19a7389 construction uses the P2 M PI Level KSplit W Semi A to Matrix  lin 81c9c19a7389 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L43-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem P2M_PI_LevelKSplit_W_SemiA_toMatrix__lin_81c9c19a7389 (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by sorry

alias «PI».«LevelKSplit».«W».«SemiA».«toMatrix'_lin» := P2M_PI_LevelKSplit_W_SemiA_toMatrix__lin_81c9c19a7389
