-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_KernelCokernelKilling_admissible_of_discrete_topology
-- name    : ReciprocityTheory.Coh.KernelCokernelKilling.admissible_of_discrete_topology
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:30.385252+00:00
-- url     : https://prove2.me/theorems/83244312-fc8a-5264-b8e1-06addd0a0158
-- title:
--   Kernel Cokernel Killing: admissible of discrete topology
-- statement:
--   The Kernel Cokernel Killing construction uses the admissible of discrete topology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ShiftA.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/ShiftA.lean#L63-L75

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.KernelCokernelKilling.admissible_of_discrete_topology {A B C : TRep R G} [DiscreteTopology A.V] [DiscreteTopology B.V]
    [DiscreteTopology C.V] (i : Pair A B) (p : Pair B C) (hi : i.φ = MonoidHom.id G)
    (hp : p.φ = MonoidHom.id G) (hinj : Injective i.u) (hex : Exact i.u p.u) (hsurj : Surjective p.u) :
    admitted i p := by sorry
