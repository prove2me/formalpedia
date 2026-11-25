-- Prove2me | Theorems.Thm_P2M_PI_LevelKSplit_W_SemiA_N_le_S__494d858967cb
-- name    : P2M_PI_LevelKSplit_W_SemiA_N_le_S__494d858967cb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:49.727162+00:00
-- url     : https://prove2.me/theorems/79649e1e-fcbc-5b7a-94e4-d028dbc5f2ae
-- title:
--   P2 M PI Level KSplit W Semi A N le S  494d858967cb: P2 M PI Level KSplit W Semi A N le S  494d858967cb
-- statement:
--   The P2 M PI Level KSplit W Semi A N le S  494d858967cb construction uses the P2 M PI Level KSplit W Semi A N le S  494d858967cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L65-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ToMatrixLin.lean#L65-L91

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

theorem P2M_PI_LevelKSplit_W_SemiA_N_le_S__494d858967cb (hP : P.IsStd σ J T) : Nsub R σ J P ≤ Ssub R σ J P := by sorry

alias «PI».«LevelKSplit».«W».«SemiA».«N_le_S'» := P2M_PI_LevelKSplit_W_SemiA_N_le_S__494d858967cb
