-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_normF_zsmul
-- name    : ReciprocityTheory.Coh.CCA.normF_zsmul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:39.533955+00:00
-- url     : https://prove2.me/theorems/0450ac81-9c16-4031-81cb-07c77bf9fa3e
-- title:
--   CCA: norm F zsmul
-- statement:
--   The CCA construction uses the norm F zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L289-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L289-L295

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

theorem ReciprocityTheory.Coh.CCA.normF_zsmul {M : TRep R G} (n : ℕ) (c : ℤ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U n (c • F) = c • normF M U n F := by sorry
