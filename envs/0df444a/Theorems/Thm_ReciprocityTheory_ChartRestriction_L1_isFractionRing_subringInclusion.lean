-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isFractionRing_subringInclusion
-- name    : ReciprocityTheory.ChartRestriction.L1.isFractionRing_subringInclusion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:34.687905+00:00
-- url     : https://prove2.me/theorems/2ebb2df3-f06d-5cac-b6ae-7bf42ee8c838
-- title:
--   L1: is Fraction Ring subring Inclusion
-- statement:
--   The L1 construction uses the is Fraction Ring subring Inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean#L103-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean#L103-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)

theorem ReciprocityTheory.ChartRestriction.L1.isFractionRing_subringInclusion (hf : ∀ x ∈ F, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x = a / b) :
    @IsFractionRing R _ F _ (subringInclusionSubfield R F h).toAlgebra := by sorry
