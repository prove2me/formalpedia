-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Glob_lin_fix_span
-- name    : PI.LevelKSplit.W.Glob.lin_fix_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:35.874857+00:00
-- url     : https://prove2.me/theorems/15baec08-47cf-4c07-9d72-3cb2dad6f505
-- title:
--   Glob: lin fix span
-- statement:
--   The Glob construction uses the lin fix span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L60-L71

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

theorem PI.LevelKSplit.W.Glob.lin_fix_span (g : HA R σ J) {m : ℕ} (Y : Fin m → Fin n → E)
    (hY : ∀ a, lin R σ J g (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E)
    (hy : y ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a))) :
    lin R σ J g y = y := by sorry
