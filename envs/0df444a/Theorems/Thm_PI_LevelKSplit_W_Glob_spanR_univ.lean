-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Glob_spanR_univ
-- name    : PI.LevelKSplit.W.Glob.spanR_univ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:22.828434+00:00
-- url     : https://prove2.me/theorems/d520e33c-c6e2-44c6-9cf8-5fcc72c76984
-- title:
--   Glob: span R univ
-- statement:
--   The Glob construction uses the span R univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L73-L76

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

theorem PI.LevelKSplit.W.Glob.spanR_univ {m : ℕ} (Y : Fin m → Fin n → E) :
    spanR (F := F) R Y Set.univ =
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by sorry
