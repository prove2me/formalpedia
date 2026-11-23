-- Prove2me | Theorems.Thm_PI_VolStabSW_CompGAux_mat_haMap_apply
-- name    : PI.VolStabSW.CompGAux.mat_haMap_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:49:45.749809+00:00
-- url     : https://prove2.me/theorems/ff8afe18-4315-4d4f-8e62-9c6b105bc026
-- title:
--   Comp GAux: mat ha Map apply
-- statement:
--   The Comp GAux construction uses the mat ha Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L58-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.CompGAux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabSW.FiniteThetaCoordinates
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem PI.VolStabSW.CompGAux.mat_haMap_apply (φ : R →ₐ[F] S) (h : HA R σ J) (i j : Fin M) :
    ((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j =
      Algebra.TensorProduct.map φ (AlgHom.id F E)
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j) := by sorry
