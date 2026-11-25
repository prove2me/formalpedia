-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ZuckHomCat_sum_nonneg__c895c5f25bf0
-- name    : P2M_GlobalTheory_CompanionTheory_ZuckHomCat_sum_nonneg__c895c5f25bf0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:50.03342+00:00
-- url     : https://prove2.me/theorems/5f70361a-a956-4bd3-823d-b97554019995
-- title:
--   P2 M Global Theory Companion Theory Zuck Hom Cat sum nonneg  c895c5f25bf0: P2 M Global Theory Companion Theory Zuck Hom Cat sum nonneg  c895c5f25bf0
-- statement:
--   The P2 M Global Theory Companion Theory Zuck Hom Cat sum nonneg  c895c5f25bf0 construction uses the P2 M Global Theory Companion Theory Zuck Hom Cat sum nonneg  c895c5f25bf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean#L37-L41

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}

theorem P2M_GlobalTheory_CompanionTheory_ZuckHomCat_sum_nonneg__c895c5f25bf0 (X : Obj k r) (Ws : List (List (Mx k r))) (x : M X) :
    0 ≤ (Ws.map fun W' => sn X W' x).sum := by sorry

alias «GlobalTheory».«CompanionTheory».«ZuckHomCat».«sum_nonneg'» := P2M_GlobalTheory_CompanionTheory_ZuckHomCat_sum_nonneg__c895c5f25bf0
