-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_mulVec
-- name    : PI.VolStabSW.FiniteThetaCoordinates.crd_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:00.632843+00:00
-- url     : https://prove2.me/theorems/334b3894-d513-4d63-ba2f-8d52912ec389
-- title:
--   Finite Theta Coordinates: crd mul Vec
-- statement:
--   The Finite Theta Coordinates construction uses the crd mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L64-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem PI.VolStabSW.FiniteThetaCoordinates.crd_mulVec (R : Type) [CommRing R] [Algebra F R] {M : ℕ}
    (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) (i : Fin M) (k : Fin d) :
    crd b R ((m.mulVec y) i) k = ∑ j, ∑ p, ∑ q, crd b R (m i j) p * crd b R (y j) q *
      algebraMap F R (b.repr (b p * b q) k) := by sorry
