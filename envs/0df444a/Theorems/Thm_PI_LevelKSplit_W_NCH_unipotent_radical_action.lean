-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_unipotent_radical_action
-- name    : PI.LevelKSplit.W.NCH.unipotent_radical_action
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:41.718626+00:00
-- url     : https://prove2.me/theorems/7a7dfc4f-54e6-5a43-be4e-bf3c2b3b3847
-- title:
--   NCH: unipotent radical action
-- statement:
--   The NCH construction uses the unipotent radical action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L175-L180

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

theorem PI.LevelKSplit.W.NCH.unipotent_radical_action {g : HA R σ J} (hg : g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P)
    {v : Fin M → R ⊗[F] E} (hv : Xp (datR R σ J P T) v) :
    lin R σ J g v = v - ∑ a, (datR R σ J P T).h (PI.LevelKSplit.W.NC.yH R σ J P g a) v •
      (datR R σ J P T).e a := by sorry
