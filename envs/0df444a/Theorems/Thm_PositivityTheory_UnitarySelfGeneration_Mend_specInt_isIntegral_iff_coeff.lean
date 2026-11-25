-- Prove2me | Theorems.Thm_PositivityTheory_UnitarySelfGeneration_Mend_specInt_isIntegral_iff_coeff
-- name    : PositivityTheory.UnitarySelfGeneration.Mend.specInt_isIntegral_iff_coeff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:05:26.541052+00:00
-- url     : https://prove2.me/theorems/ffbcb7a1-974c-4c88-9a9e-24c0f29a4350
-- title:
--   Mend: spec Int is Integral iff coeff
-- statement:
--   The Mend construction uses the spec Int is Integral iff coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HomogeneousNonvanishing/SpectralNormIntegrality/SpecInt.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/HomogeneousNonvanishing/SpectralNormIntegrality/SpecInt.lean#L15-L29

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
open Polynomial

theorem PositivityTheory.UnitarySelfGeneration.Mend.specInt_isIntegral_iff_coeff {K L : Type*} [Field K] [Field L] [Algebra K L] (O : ValuationSubring K)
    [Algebra O L] [IsScalarTower O K L] (y : L) (hy : IsIntegral K y) :
    IsIntegral O y ↔ ∀ n, (minpoly K y).coeff n ∈ O := by sorry
