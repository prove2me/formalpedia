-- Prove2me | Theorems.Thm_PI_VolStabW_IdxHW_cr_sig
-- name    : PI.VolStabW.IdxHW.cr_sig
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:13.137452+00:00
-- url     : https://prove2.me/theorems/2201a7e4-c870-4044-8b4f-e4a0a01f825d
-- title:
--   Idx HW: cr sig
-- statement:
--   The Idx HW construction uses the cr sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxC.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensIdxC.lean#L38-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem PI.VolStabW.IdxHW.cr_sig (y : Fv F v ⊗[F] E) (k : Fin 2) :
    cr b v (sigR (Fv F v) σ y) k = ∑ l, algebraMap F (Fv F v) (Cmat b σ k l) * cr b v y l := by sorry
