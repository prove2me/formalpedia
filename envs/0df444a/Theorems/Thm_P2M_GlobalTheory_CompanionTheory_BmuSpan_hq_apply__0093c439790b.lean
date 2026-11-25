-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_BmuSpan_hq_apply__0093c439790b
-- name    : P2M_GlobalTheory_CompanionTheory_BmuSpan_hq_apply__0093c439790b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:13.198975+00:00
-- url     : https://prove2.me/theorems/7560307b-3476-4e78-904b-4789b5ac0d6b
-- title:
--   P2 M Global Theory Companion Theory Bmu Span hq apply  0093c439790b: P2 M Global Theory Companion Theory Bmu Span hq apply  0093c439790b
-- statement:
--   The P2 M Global Theory Companion Theory Bmu Span hq apply  0093c439790b construction uses the P2 M Global Theory Companion Theory Bmu Span hq apply  0093c439790b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SpanGenerators.lean#L68-L72

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfIwasawaLeviCartan
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SpanGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu GlobalTheory.CompanionTheory.BmuDecomp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuSpan
variable {k r : ℕ}

theorem P2M_GlobalTheory_CompanionTheory_BmuSpan_hq_apply__0093c439790b (i j : Fin (2 * r + k + 1)) : Hq k r i j = if i = pr k r j then 1 else 0 := by sorry

alias «GlobalTheory».«CompanionTheory».«BmuSpan».«hq_apply'» := P2M_GlobalTheory_CompanionTheory_BmuSpan_hq_apply__0093c439790b
