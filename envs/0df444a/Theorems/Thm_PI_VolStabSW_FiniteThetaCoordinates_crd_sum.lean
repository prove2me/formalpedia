-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_crd_sum
-- name    : PI.VolStabSW.FiniteThetaCoordinates.crd_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:33.006922+00:00
-- url     : https://prove2.me/theorems/f835fba1-58bb-4ada-8167-b1243af28b0f
-- title:
--   Finite Theta Coordinates: crd sum
-- statement:
--   The Finite Theta Coordinates construction uses the crd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L37-L39

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

theorem PI.VolStabSW.FiniteThetaCoordinates.crd_sum (R : Type) [CommRing R] [Algebra F R] {ι : Type} (s : Finset ι) (y : ι → R ⊗[F] E)
    (k : Fin d) : crd b R (∑ i ∈ s, y i) k = ∑ i ∈ s, crd b R (y i) k := by sorry
