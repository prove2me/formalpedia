-- Prove2me | Theorems.Thm_PI_VolStabW_AdmissibleCompactSupport_crd_projV
-- name    : PI.VolStabW.AdmissibleCompactSupport.crd_projV
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:51.358811+00:00
-- url     : https://prove2.me/theorems/81d3d8f4-7e51-4cb2-b646-6f204a8431fd
-- title:
--   Admissible Compact Support: crd proj V
-- statement:
--   The Admissible Compact Support construction uses the crd proj V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/AdmCpt.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/AdmCpt.lean#L18-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuNeSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_AdmCpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.AdmissibleCompactSupport
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open PI.VolStabW PI.VolStabW.PositiveNearLattice Set Filter
open scoped TensorProduct RestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem PI.VolStabW.AdmissibleCompactSupport.crd_projV {a M : ℕ} (Y : Fin a → Fin M → Af F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F))
    (i : Fin a) (j : Fin M) (k : Fin d) :
    crd b (Fv F v) (projV v Y i j) k = (crd b (Af F) (Y i j) k) v := by sorry
