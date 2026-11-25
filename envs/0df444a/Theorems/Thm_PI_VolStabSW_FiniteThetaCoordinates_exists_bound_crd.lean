-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_exists_bound_crd
-- name    : PI.VolStabSW.FiniteThetaCoordinates.exists_bound_crd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:01.007326+00:00
-- url     : https://prove2.me/theorems/0100f90c-5720-48a7-99b8-e1b0db801857
-- title:
--   Finite Theta Coordinates: exists bound crd
-- statement:
--   The Finite Theta Coordinates construction uses the exists bound crd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L106-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L106-L136

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

theorem PI.VolStabSW.FiniteThetaCoordinates.exists_bound_crd {R K : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [NormedField K] (φ : R →+* K) (hφ : Continuous φ) {a M : ℕ}
    {S : Set (Fin a → Fin M → R ⊗[F] E)} (hS : IsCompact S) :
    ∃ B, 0 ≤ B ∧ ∀ Y ∈ S, ∀ i j k, ‖φ (crd b R (Y i j) k)‖ ≤ B := by sorry
