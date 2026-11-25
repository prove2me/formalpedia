-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_admissible_chain_inf
-- name    : ReciprocityTheory.Coh.ContinuousSections.admissible_chain_inf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:51:32.046597+00:00
-- url     : https://prove2.me/theorems/b69e0b8d-00e3-45fc-b42e-0f179aba7064
-- title:
--   Continuous Sections: admissible chain inf
-- statement:
--   The Continuous Sections construction uses the admissible chain inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/SectionA.lean#L85-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/SectionA.lean#L85-L115

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise Set
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.ContinuousSections
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.ContinuousSections.admissible_chain_inf [CompactSpace G] (U : Subgroup G) (hU : IsClosed (U : Set G))
    (c : Set (Subgroup G × Set G)) (hc : ∀ p ∈ c, admitted U p)
    (htot : ∀ p ∈ c, ∀ q ∈ c, p ≤ q ∨ q ≤ p) (y : Subgroup G × Set G) (hy : y ∈ c) :
    admitted U (⨅ p ∈ c, p.1, ⋂ p ∈ c, p.2) := by sorry
