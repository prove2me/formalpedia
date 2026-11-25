-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_normF_sub
-- name    : ReciprocityTheory.Coh.CCA.normF_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:20.608439+00:00
-- url     : https://prove2.me/theorems/d2cd266b-c38b-57f8-b4b5-c386ad54cba8
-- title:
--   CCA: norm F sub
-- statement:
--   The CCA construction uses the norm F sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L281-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L281-L287

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
variable [U.FiniteIndex]

theorem ReciprocityTheory.Coh.CCA.normF_sub {M : TRep R G} (n : ℕ) (F F' : (Fin (n + 1) → G) → M.V) :
    normF M U n (F - F') = normF M U n F - normF M U n F' := by sorry
