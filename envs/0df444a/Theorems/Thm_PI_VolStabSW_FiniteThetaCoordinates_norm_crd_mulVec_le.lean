-- Prove2me | Theorems.Thm_PI_VolStabSW_FiniteThetaCoordinates_norm_crd_mulVec_le
-- name    : PI.VolStabSW.FiniteThetaCoordinates.norm_crd_mulVec_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:49.384638+00:00
-- url     : https://prove2.me/theorems/ec50c035-4d79-51eb-a5a3-82d529cb2f8b
-- title:
--   Finite Theta Coordinates: norm crd mul Vec le
-- statement:
--   The Finite Theta Coordinates construction uses the norm crd mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L70-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/FinTheta.lean#L70-L90

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

theorem PI.VolStabSW.FiniteThetaCoordinates.norm_crd_mulVec_le {R K : Type} [CommRing R] [Algebra F R] [NormedField K] (φ : R →+* K)
    {M : ℕ} (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) {A B C : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ i j p, ‖φ (crd b R (m i j) p)‖ ≤ A) (hB : ∀ j q, ‖φ (crd b R (y j) q)‖ ≤ B)
    (hC : ∀ p q k, ‖φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ C) (i : Fin M) (k : Fin d) :
    ‖φ (crd b R ((m.mulVec y) i) k)‖ ≤ M * (d * (d * (A * B * C))) := by sorry
