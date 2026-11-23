-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_isClosed_stabT
-- name    : PI.VolSemiDirect.W.isClosed_stabT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:08.813886+00:00
-- url     : https://prove2.me/theorems/17d20cc1-1bdd-4942-8e86-34e37b1526b5
-- title:
--   W: is Closed stab T
-- statement:
--   The W construction uses the is Closed stab T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L112-L119

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_Closed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R}
variable (R)

theorem PI.VolSemiDirect.W.isClosed_stabT [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {a : ℕ}
    (X : Fin a → Fin n → E) : IsClosed (stabT R σ J X : Set (HA R σ J)) := by sorry
