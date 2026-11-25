-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_SemiA_mul_inv_piG_mem_N
-- name    : PI.LevelKSplit.W.SemiA.mul_inv_piG_mem_N
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:21.864277+00:00
-- url     : https://prove2.me/theorems/0e2a8336-1e1e-581a-9ca8-9b3c7c604a34
-- title:
--   Semi A: mul inv pi G mem N
-- statement:
--   The Semi A construction uses the mul inv pi G mem N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulInvPiGMemN.lean#L96-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulInvPiGMemN.lean#L96-L123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
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
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem PI.LevelKSplit.W.SemiA.mul_inv_piG_mem_N {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    s * (piG hσσ hJ hP s hs)⁻¹ ∈ Nsub R σ J P := by sorry
