-- Prove2me | Theorems.Thm_PI_VolStabSW_CompGAux_map_smul_tup
-- name    : PI.VolStabSW.CompGAux.map_smul_tup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:49.754773+00:00
-- url     : https://prove2.me/theorems/60970cd2-9377-51fd-a166-04acbbfb75c0
-- title:
--   Comp GAux: map smul tup
-- statement:
--   The Comp GAux construction uses the map smul tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean#L63-L69

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

theorem PI.VolStabSW.CompGAux.map_smul_tup (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by sorry
