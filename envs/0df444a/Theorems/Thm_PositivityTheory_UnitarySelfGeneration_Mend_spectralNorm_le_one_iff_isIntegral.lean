-- Prove2me | Theorems.Thm_PositivityTheory_UnitarySelfGeneration_Mend_spectralNorm_le_one_iff_isIntegral
-- name    : PositivityTheory.UnitarySelfGeneration.Mend.spectralNorm_le_one_iff_isIntegral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:24.568088+00:00
-- url     : https://prove2.me/theorems/097a5d1a-b047-45c8-9cee-e58eb409fc0c
-- title:
--   Mend: spectral Norm le one iff is Integral
-- statement:
--   The Mend construction uses the spectral Norm le one iff is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HomogeneousNonvanishing/SpectralNormIntegrality/SpecInt.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HomogeneousNonvanishing/SpectralNormIntegrality/SpecInt.lean#L31-L38

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

theorem PositivityTheory.UnitarySelfGeneration.Mend.spectralNorm_le_one_iff_isIntegral (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (y : AlgebraicClosure (v.adicCompletion F)) :
    spectralNorm (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) y ≤ 1 ↔
      IsIntegral (v.adicCompletionIntegers F) y := by sorry
