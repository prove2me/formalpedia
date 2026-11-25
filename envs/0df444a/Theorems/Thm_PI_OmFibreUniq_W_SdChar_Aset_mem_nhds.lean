-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdChar_Aset_mem_nhds
-- name    : PI.OmFibreUniq.W.SdChar.Aset_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:56.437802+00:00
-- url     : https://prove2.me/theorems/fb02d87d-c135-4380-86ea-2a8cc12ea30b
-- title:
--   Sd Char: Aset mem nhds
-- statement:
--   The Sd Char construction uses the Aset mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExChar.lean#L97-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExChar.lean#L97-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdChar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
  (hψn : ∀ r, ‖ψ0 r‖ = 1)
include hψc hψa hψn

theorem PI.OmFibreUniq.W.SdChar.Aset_mem_nhds : Aset v ψ0 ∈ 𝓝 (0 : Fv F v) := by sorry
