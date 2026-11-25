-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_heisenberg_cocycle_mem_centre
-- name    : PI.LevelKSplit.W.NCH.heisenberg_cocycle_mem_centre
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:27.325265+00:00
-- url     : https://prove2.me/theorems/f6509316-6e93-5cdd-82f1-a08391c96e8d
-- title:
--   NCH: heisenberg cocycle mem centre
-- statement:
--   The NCH construction uses the heisenberg cocycle mem centre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L243-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L243-L258

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
variable (hJ : IsHermND σ J) (H : (datR R σ J P T).Hyp) {half : R ⊗[F] E}
  (hh : Half (datR R σ J P T) half)
include hJ H hh

theorem PI.LevelKSplit.W.NCH.heisenberg_cocycle_mem_centre {y y' : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hy' : ∀ a, IsWp (datR R σ J P T) (y' a)) (hyy : ∀ a, IsWp (datR R σ J P T) ((y + y') a)) :
    sHG hJ H hh hy * sHG hJ H hh hy' * (sHG hJ H hh hyy)⁻¹ ∈ PI.LevelKSplit.W.NC.Zsub R σ J P := by sorry
