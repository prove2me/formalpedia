-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_isClosed_spanR
-- name    : PI.VolSemiDirect.W.isClosed_spanR
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:01.694659+00:00
-- url     : https://prove2.me/theorems/50b81b29-a7e0-4bf0-94a4-e045c2f762cf
-- title:
--   W: is Closed span R
-- statement:
--   The W construction uses the is Closed span R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L99-L108

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

theorem PI.VolSemiDirect.W.isClosed_spanR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {m : ℕ}
    (Y : Fin m → Fin n → E) (s : Set (Fin m)) :
    IsClosed (spanR (F := F) R Y s : Set (Fin n → R ⊗[F] E)) := by sorry
