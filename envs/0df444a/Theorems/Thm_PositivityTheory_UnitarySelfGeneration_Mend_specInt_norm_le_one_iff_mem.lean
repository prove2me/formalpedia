-- Prove2me | Theorems.Thm_PositivityTheory_UnitarySelfGeneration_Mend_specInt_norm_le_one_iff_mem
-- name    : PositivityTheory.UnitarySelfGeneration.Mend.specInt_norm_le_one_iff_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:28.927806+00:00
-- url     : https://prove2.me/theorems/f8936906-4194-44fd-bdcc-17b5d7d229b0
-- title:
--   Mend: spec Int norm le one iff mem
-- statement:
--   The Mend construction uses the spec Int norm le one iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HomogeneousNonvanishing/SpectralNormIntegrality/SpecInt.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HomogeneousNonvanishing/SpectralNormIntegrality/SpecInt.lean#L9-L12

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HomogeneousNonvanishing_SpectralNormIntegrality_SpecInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.UnitarySelfGeneration PositivityTheory.UnitarySelfGeneration.Mend

theorem PositivityTheory.UnitarySelfGeneration.Mend.specInt_norm_le_one_iff_mem (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by sorry
