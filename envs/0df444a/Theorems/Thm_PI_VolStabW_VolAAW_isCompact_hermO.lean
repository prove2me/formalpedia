-- Prove2me | Theorems.Thm_PI_VolStabW_VolAAW_isCompact_hermO
-- name    : PI.VolStabW.VolAAW.isCompact_hermO
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:02.954337+00:00
-- url     : https://prove2.me/theorems/59bbe07f-14f7-5678-add9-5f2e0023f340
-- title:
--   Vol AAW: is Compact herm O
-- statement:
--   The Vol AAW construction uses the is Compact herm O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolC.lean#L92-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/LocDensVolC.lean#L92-L110

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

theorem PI.VolStabW.VolAAW.isCompact_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) ∧
      IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by sorry
