-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCL_pXv_of_span
-- name    : PI.LevelKSplit.W.NCL.pXv_of_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:03.580817+00:00
-- url     : https://prove2.me/theorems/7834f4a1-6004-4411-aad3-1e433bb0c712
-- title:
--   NCL: p Xv of span
-- statement:
--   The NCL construction uses the p Xv of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean#L194-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LeviInfUnipotentEqOne.lean#L194-L204

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
variable (R σ J P)
variable {R σ J P}

theorem PI.LevelKSplit.W.NCL.pXv_of_span (H : (datR R σ J P T).Hyp) {x : Fin M → R ⊗[F] E}
    (hx : x ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).f)) :
    (datR R σ J P T).pXv x = x := by sorry
