-- Prove2me | Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_mulVec
-- name    : PI.VolStabW.FiniteThetaCoordinates.crd_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:27.807136+00:00
-- url     : https://prove2.me/theorems/33eab4cd-656f-4974-b156-776efb0ef476
-- title:
--   Finite Theta Coordinates: crd mul Vec
-- statement:
--   The Finite Theta Coordinates construction uses the crd mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/FinTheta.lean#L64-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem PI.VolStabW.FiniteThetaCoordinates.crd_mulVec (R : Type) [CommRing R] [Algebra F R] {M : ℕ}
    (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) (i : Fin M) (k : Fin d) :
    crd b R ((m.mulVec y) i) k = ∑ j, ∑ p, ∑ q, crd b R (m i j) p * crd b R (y j) q *
      algebraMap F R (b.repr (b p * b q) k) := by sorry
