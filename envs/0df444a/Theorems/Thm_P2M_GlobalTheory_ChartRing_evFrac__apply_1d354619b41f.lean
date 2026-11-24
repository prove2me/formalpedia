-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f
-- name    : P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:46:02.19178+00:00
-- url     : https://prove2.me/theorems/8374617a-5dfe-45a4-8859-6e632ad9225c
-- title:
--   P2 M Global Theory Chart Ring ev Frac  apply 1d354619b41f: P2 M Global Theory Chart Ring ev Frac  apply 1d354619b41f
-- statement:
--   The P2 M Global Theory Chart Ring ev Frac  apply 1d354619b41f construction uses the P2 M Global Theory Chart Ring ev Frac  apply 1d354619b41f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsPrincipalIdealRingOfIsLocalization.lean#L268-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsPrincipalIdealRingOfIsLocalization.lean#L268-L269

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IrreducibleSpacePrimeSpectrumAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsPrincipalIdealRingOfIsLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O]
variable (hπ : Irreducible π)
variable (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
  (U : Type*) [CommRing U] [Algebra O⟦X⟧ U] [IsLocalization.Away (C π * X : O⟦X⟧) U]

theorem P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f [Algebra O U] [IsScalarTower O O⟦X⟧ U] (z : U) :
    evFracₐ hπ K U z = evFrac hπ K U z := by sorry

alias «GlobalTheory».«ChartRing».«evFracₐ_apply» := P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f

attribute [defeq] P2M_GlobalTheory_ChartRing_evFrac__apply_1d354619b41f
