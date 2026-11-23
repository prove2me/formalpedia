-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_isClosed_Nsub
-- name    : PI.VolSemiDirect.W.isClosed_Nsub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:06.158993+00:00
-- url     : https://prove2.me/theorems/dbc56594-29fc-4464-b296-1b613dd4dd89
-- title:
--   W: is Closed Nsub
-- statement:
--   The W construction uses the is Closed Nsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L121-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L121-L133

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

theorem PI.VolSemiDirect.W.isClosed_Nsub [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {r : ℕ}
    (P : Frame E n r) : IsClosed (Nsub R σ J P : Set (HA R σ J)) := by sorry
