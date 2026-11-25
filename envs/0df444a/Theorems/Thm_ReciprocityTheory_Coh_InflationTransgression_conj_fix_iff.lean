-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_InflationTransgression_conj_fix_iff
-- name    : ReciprocityTheory.Coh.InflationTransgression.conj_fix_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:51:37.174145+00:00
-- url     : https://prove2.me/theorems/9edee16e-84d5-48b9-873b-209d3b682607
-- title:
--   Inflation Transgression: conj fix iff
-- statement:
--   The Inflation Transgression construction uses the conj fix iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionB.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/TransgressionB.lean#L34-L39

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

theorem ReciprocityTheory.Coh.InflationTransgression.conj_fix_iff (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) :
    (conjN M N s).hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf ↔
      ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := by sorry
