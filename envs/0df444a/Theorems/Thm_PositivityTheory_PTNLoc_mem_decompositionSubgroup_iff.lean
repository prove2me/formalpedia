-- Prove2me | Theorems.Thm_PositivityTheory_PTNLoc_mem_decompositionSubgroup_iff
-- name    : PositivityTheory.PTNLoc.mem_decompositionSubgroup_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:35.591887+00:00
-- url     : https://prove2.me/theorems/650715c1-127f-5234-bf21-10d604b2c7e1
-- title:
--   PTNLoc: mem decomposition Subgroup iff
-- statement:
--   The PTNLoc construction uses the mem decomposition Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/MemDecompositionSubgroupIff.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/MemDecompositionSubgroupIff.lean#L10-L22

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_MemDecompositionSubgroupIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso Pointwise
open PositivityTheory PositivityTheory.PTNLoc

theorem PositivityTheory.PTNLoc.mem_decompositionSubgroup_iff {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (A : ValuationSubring Ω) (σ : G F Ω) :
    σ ∈ A.decompositionSubgroup F ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by sorry
