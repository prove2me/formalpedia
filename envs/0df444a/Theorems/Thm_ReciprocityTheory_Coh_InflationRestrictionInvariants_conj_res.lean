-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_conj_res
-- name    : ReciprocityTheory.Coh.InflationRestrictionInvariants.conj_res
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:51:51.006117+00:00
-- url     : https://prove2.me/theorems/e8f6dc40-ba9b-4bd2-81ea-ba2e5f441f74
-- title:
--   Inflation Restriction Invariants: conj res
-- statement:
--   The Inflation Restriction Invariants construction uses the conj res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L250-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/InfRes.lean#L250-L264

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
open ReciprocityTheory.Gal Cx Function
universe u
noncomputable section
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.InflationRestrictionInvariants.conj_res (M : TRep R G) (N : Subgroup G) (s : G) (c : Pair (M.resSub N) (M.resSub N))
    (hc : ∀ g, (c.φ g : G) = s⁻¹ * g * s) (hu : ∀ m, c.u m = M.rho s m) (n : ℕ) (x : M.H n) :
    c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x := by sorry
