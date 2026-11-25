-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_exists_lift
-- name    : ReciprocityTheory.Coh.InflationTransgression.exists_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:31.290236+00:00
-- url     : https://prove2.me/theorems/840f3038-bdf4-4ad3-92f1-7338b5aed994
-- title:
--   Inflation Transgression: exists lift
-- statement:
--   The Inflation Transgression construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionB.lean#L167-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionB.lean#L167-L188

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationTransgression
open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP

theorem ReciprocityTheory.Coh.InflationTransgression.exists_lift [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [DiscreteTopology M.V]
    (hNc : IsClosed (N : Set G)) (f0 : (M.resSub N).coch.X 1) (hf : (M.resSub N).coch.d 1 f0 = 0)
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), M.coch.d 1 y = P.hom.f 2 z ∧
      (Pair.res M N.subtype continuous_subtype_val).hom.f 1 y = f0 := by sorry
