-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Glob_H_fix_e
-- name    : PI.LevelKSplit.W.Glob.H_fix_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:35.59297+00:00
-- url     : https://prove2.me/theorems/3db1a333-e21e-4125-ab1b-f9635d3a6453
-- title:
--   Glob: H fix e
-- statement:
--   The Glob construction uses the H fix e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L85-L88

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

theorem PI.LevelKSplit.W.Glob.H_fix_e {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by sorry
