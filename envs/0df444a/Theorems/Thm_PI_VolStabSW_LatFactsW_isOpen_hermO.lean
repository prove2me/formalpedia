-- Prove2me | Theorems.Thm_PI_VolStabSW_LatFactsW_isOpen_hermO
-- name    : PI.VolStabSW.LatFactsW.isOpen_hermO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:40:49.570882+00:00
-- url     : https://prove2.me/theorems/7bc80f00-2a0e-48e5-ac35-13a05f96bb87
-- title:
--   Lat Facts W: is Open herm O
-- statement:
--   The Lat Facts W construction uses the is Open herm O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHL.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/LocDensHL.lean#L25-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnifVSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHL
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
open PI.VolStabSW.LatFactsW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem PI.VolStabSW.LatFactsW.isOpen_hermO (σ : E →ₐ[F] E) (a : ℕ) : IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by sorry
