-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_Nsub
-- name    : PI.LevelKSplit.W.ExC.isClosed_Nsub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:16.947928+00:00
-- url     : https://prove2.me/theorems/eefbcc37-306e-4f4d-bdab-5a1795333fd7
-- title:
--   Ex C: is Closed Nsub
-- statement:
--   The Ex C construction uses the is Closed Nsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnitaryGroupSecondCountableT2.lean#L164-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnitaryGroupSecondCountableT2.lean#L164-L178

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem PI.LevelKSplit.W.ExC.isClosed_Nsub (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r)
    (T : F) (hP : P.IsStd σ J T) :
    IsClosed (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) := by sorry
