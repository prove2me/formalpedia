-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_H_conj_sHG
-- name    : PI.LevelKSplit.W.NCH.H_conj_sHG
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:49.586377+00:00
-- url     : https://prove2.me/theorems/8b890181-0e7c-59d0-a615-9211b4f44766
-- title:
--   NCH: H conj s HG
-- statement:
--   The NCH construction uses the H conj s HG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L288-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L288-L306

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

theorem PI.LevelKSplit.W.NCH.H_conj_sHG {g : HA R σ J} (hg : g ∈ Hsub R σ J P) {y : Fin r → Fin M → R ⊗[F] E}
    (hy : ∀ a, IsWp (datR R σ J P T) (y a))
    (hyh : ∀ a, IsWp (datR R σ J P T) ((fun b => lin R σ J g (y b)) a)) :
    g * sHG hJ H hh hy * g⁻¹ = sHG hJ H hh hyh := by sorry
