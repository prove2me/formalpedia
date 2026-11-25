-- Prove2me | Theorems.Thm_PI_VolStabW_VolAAW_crd_sigR
-- name    : PI.VolStabW.VolAAW.crd_sigR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:41:59.13071+00:00
-- url     : https://prove2.me/theorems/7588b351-473d-59ee-ac19-15d76334086d
-- title:
--   Vol AAW: crd sig R
-- statement:
--   The Vol AAW construction uses the crd sig R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolC.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolC.lean#L18-L31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC
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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabW.VolAAW.crd_sigR (σ : E →ₐ[F] E) (z : Fv F v ⊗[F] E) (l : Fin d) :
    crd b (Fv F v) (sigR (Fv F v) σ z) l =
      ∑ k, crd b (Fv F v) z k * algebraMap F (Fv F v) (b.repr (σ (b k)) l) := by sorry
