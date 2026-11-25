-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Glob_phiV_span
-- name    : PI.LevelKSplit.W.Glob.phiV_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:39.240318+00:00
-- url     : https://prove2.me/theorems/15cbe4db-e50f-40e8-b4b6-9869ca0c5b4a
-- title:
--   Glob: phi V span
-- statement:
--   The Glob construction uses the phi V span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L132-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/RatVMemSpan.lean#L132-L153

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem PI.LevelKSplit.W.Glob.phiV_span (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (Y : Fin m → Fin n → E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ spanR (F := F) (Af F) Y Set.univ) :
    (fun i => phiV v (y i)) ∈
      Submodule.span (Fv F v ⊗[F] E) (Set.range fun a => ratV (F := F) (Fv F v) (Y a)) := by sorry
