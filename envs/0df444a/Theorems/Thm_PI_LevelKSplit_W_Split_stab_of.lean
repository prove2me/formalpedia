-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Split_stab_of
-- name    : PI.LevelKSplit.W.Split.stab_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:38.094676+00:00
-- url     : https://prove2.me/theorems/bb3c3a84-3acb-4073-a332-e5fd13de5bbf
-- title:
--   Split: stab of
-- statement:
--   The Split construction uses the stab of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfExistSMeasKf.lean#L15-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/LevelSAllOfExistSMeasKf.lean#L15-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Split
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem PI.LevelKSplit.W.Split.stab_of (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (ΛX ΛW ΛY : Set (Fin n → E)) (hA : Adapted F E σ n J P ΛX ΛW ΛY)
    (k g : HA (Af F) σ J) (hk : k ∈ Hsub (Af F) σ J P) (hg : g ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY))
    (hgk : ∀ w ∈ ΛW, lin (Af F) σ J g (ratV (F := F) (Af F) w) -
      lin (Af F) σ J k (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∀ x ∈ latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY),
      Matrix.mulVec ((compV v (incAf σ J k) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY) := by sorry
