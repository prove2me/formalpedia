-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_RightCosetSpaceCompact_exists_isCompact_subset_mk_image__602cb71fd151
-- name    : P2M_UpperTheory_Reformulated_B_RightCosetSpaceCompact_exists_isCompact_subset_mk_image__602cb71fd151
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:44:39.590939+00:00
-- url     : https://prove2.me/theorems/dc950127-674c-4d59-a985-ea03134079a5
-- title:
--   P2 M Upper Theory Reformulated B Right Coset Space Compact exists is Compact subset mk image  602cb71fd151: P2 M Upper Theory Reformulated B Right Coset Space Compact exists is Compact subset mk image
-- statement:
--   The P2 M Upper Theory Reformulated B Right Coset Space Compact exists is Compact subset mk image  602cb71fd151 construction uses the P2 M Upper Theory Reformulated B Right Coset Space Compact exists is Compact subset mk image  602cb71fd151 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/RightCosetSpaceCompact.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/RightCosetSpaceCompact.lean#L11-L30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RightCosetSpaceCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_RightCosetSpaceCompact_exists_isCompact_subset_mk_image__602cb71fd151.{u_1} :
    ∀ {G : Type u_1} [inst : Group G] (Γ : Subgroup G) [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] {K : Set (UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ)},
      IsCompact K → ∃ (D : Set G), IsCompact D ∧ K ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D := by sorry

alias «UpperTheory».«Reformulated».«B».«RightCosetSpaceCompact».«exists_isCompact_subset_mk_image».«» := P2M_UpperTheory_Reformulated_B_RightCosetSpaceCompact_exists_isCompact_subset_mk_image__602cb71fd151
