-- Prove2me | Theorems.Thm_PI_HeckeProdW_exists_strictHenselian_absolutely_closed_local_ring
-- name    : PI.HeckeProdW.exists_strictHenselian_absolutely_closed_local_ring
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:54.397535+00:00
-- url     : https://prove2.me/theorems/43061efe-148f-5aa0-83a4-b3dab6c96db9
-- title:
--   Hecke Prod W: exists strict Henselian absolutely closed local ring
-- statement:
--   The Hecke Prod W construction uses the exists strict Henselian absolutely closed local ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean#L42-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HeckeLocalProduct/Kernel.lean#L42-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Lemmata_MiscLemmasM_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HeckeLocalProduct_Kernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct Topology
open PI PI.HeckeProdW
variable (L : Type) [Field L] [NumberField L]
variable {L}

theorem PI.HeckeProdW.exists_strictHenselian_absolutely_closed_local_ring (χ : HChar L) : ∃ T : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ y : Pu L, (∀ v ∈ T, y v = 1) → χ.1 (Phi L y) = 1 := by sorry
