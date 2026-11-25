-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_mul
-- name    : PI.VolStabSW.FiniteThetaCoordinates.crd_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:39:15.217405+00:00
-- url     : https://prove2.me/theorems/93dee570-6a13-53c2-816e-e860cb7db2bd
-- title:
--   Finite Theta Coordinates: crd mul
-- statement:
--   The Finite Theta Coordinates construction uses the crd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L47-L56

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

theorem PI.VolStabSW.FiniteThetaCoordinates.crd_mul (R : Type) [CommRing R] [Algebra F R] (y z : R ⊗[F] E) (k : Fin d) :
    crd b R (y * z) k = ∑ i, ∑ j, crd b R y i * crd b R z j *
      algebraMap F R (b.repr (b i * b j) k) := by sorry
