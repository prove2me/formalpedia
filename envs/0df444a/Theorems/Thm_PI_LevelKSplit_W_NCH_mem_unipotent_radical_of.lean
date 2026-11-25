-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCH_mem_unipotent_radical_of
-- name    : PI.LevelKSplit.W.NCH.mem_unipotent_radical_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:50.323841+00:00
-- url     : https://prove2.me/theorems/8509c042-694a-5c10-a70b-c961d6b3915f
-- title:
--   NCH: mem unipotent radical of
-- statement:
--   The NCH construction uses the mem unipotent radical of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean#L69-L79

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

theorem PI.LevelKSplit.W.NCH.mem_unipotent_radical_of {g : HA R σ J}
    (he : ∀ a, lin R σ J g ((datR R σ J P T).e a) = (datR R σ J P T).e a)
    (hp : ∀ v, Xp (datR R σ J P T) v →
      lin R σ J g v - v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e)) :
    g ∈ PI.LevelKSplit.W.NC.LevelUnipotentSubgroup R σ J P := by sorry
