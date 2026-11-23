-- Prove2me | Theorems.Thm_PI_VolStabS_isUnit_det_hermOf
-- name    : PI.VolStabS.isUnit_det_hermOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:16.152486+00:00
-- url     : https://prove2.me/theorems/28f8f818-4e7d-448b-bc64-726de24d83ad
-- title:
--   Vol Stab S: is Unit det herm Of
-- statement:
--   The Vol Stab S construction uses the is Unit det herm Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/TensTop.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/TensTop.lean#L216-L221

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem PI.VolStabS.isUnit_det_hermOf (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) :
    IsUnit ((hermOf R σ T hT : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) := by sorry
