-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Glob_H_perp
-- name    : PI.LevelKSplit.W.Glob.H_perp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:29.280799+00:00
-- url     : https://prove2.me/theorems/a5aa544e-d4ba-482f-994e-a00b521af839
-- title:
--   Glob: H perp
-- statement:
--   The Glob construction uses the H perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L95-L107

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

theorem PI.LevelKSplit.W.Glob.H_perp {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (w : Fin n → E)
    (hw : ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) (b : Fin r) :
    covR R σ J (P.e b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 ∧
      covR R σ J (P.f b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by sorry
