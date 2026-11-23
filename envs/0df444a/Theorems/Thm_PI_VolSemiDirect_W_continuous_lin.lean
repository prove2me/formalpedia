-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_continuous_lin
-- name    : PI.VolSemiDirect.W.continuous_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:36.153043+00:00
-- url     : https://prove2.me/theorems/a0be2e30-73ac-4cbc-a282-968248e1ac33
-- title:
--   W: continuous lin
-- statement:
--   The W construction uses the continuous lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/Closed.lean#L16-L22

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

theorem PI.VolSemiDirect.W.continuous_lin [IsTopologicalRing (R ⊗[F] E)] (x : Fin n → R ⊗[F] E) :
    Continuous fun g : HA R σ J => lin R σ J g x := by sorry
