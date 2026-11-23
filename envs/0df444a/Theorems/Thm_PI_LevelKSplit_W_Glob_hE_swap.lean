-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Glob_hE_swap
-- name    : PI.LevelKSplit.W.Glob.hE_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:46.48791+00:00
-- url     : https://prove2.me/theorems/ff7ce1c0-c58c-45c4-be84-0ab04cf2c420
-- title:
--   Glob: h E swap
-- statement:
--   The Glob construction uses the h E swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L78-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R σ J}

theorem PI.LevelKSplit.W.Glob.hE_swap (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by sorry
