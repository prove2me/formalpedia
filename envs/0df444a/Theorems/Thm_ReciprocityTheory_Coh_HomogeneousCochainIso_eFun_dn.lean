-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_HomogeneousCochainIso_eFun_dn
-- name    : ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_dn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:25.518181+00:00
-- url     : https://prove2.me/theorems/7bd31360-d667-4fd8-b349-e4ea19f6fadf
-- title:
--   Homogeneous Cochain Iso: e Fun dn
-- statement:
--   The Homogeneous Cochain Iso construction uses the e Fun dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean#L133-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean#L133-L142

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
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
open ReciprocityTheory.Coh.HomogeneousCochainIso
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_dn (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) :
    eFun M (n + 1) (dn M.rho n f) = hd n (eFun M n f) := by sorry
