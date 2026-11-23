-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_spanR
-- name    : PI.LevelKSplit.W.ExC.isClosed_spanR
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:29:15.156127+00:00
-- url     : https://prove2.me/theorems/62f6b34a-6331-4c0c-83ab-e4ac1a2c92fd
-- title:
--   Ex C: is Closed span R
-- statement:
--   The Ex C construction uses the is Closed span R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnitaryGroupSecondCountableT2.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/UnitaryGroupSecondCountableT2.lean#L135-L141

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

theorem PI.LevelKSplit.W.ExC.isClosed_spanR {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) (Af F) Y s : Set (Fin n → Af F ⊗[F] E)) := by sorry
