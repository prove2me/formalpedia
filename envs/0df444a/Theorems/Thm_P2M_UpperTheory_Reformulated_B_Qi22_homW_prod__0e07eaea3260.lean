-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
-- name    : P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:51.873647+00:00
-- url     : https://prove2.me/theorems/86b06f02-f9a2-408a-bd1b-33e7964ad027
-- title:
--   P2 M Upper Theory Reformulated B Qi22 hom W prod  0e07eaea3260: P2 M Upper Theory Reformulated B Qi22 hom W prod  0e07eaea3260
-- statement:
--   The P2 M Upper Theory Reformulated B Qi22 hom W prod  0e07eaea3260 construction uses the P2 M Upper Theory Reformulated B Qi22 hom W prod  0e07eaea3260 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HomWProd.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HomWProd.lean#L40-L54

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HomWProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qi22».«homW_prod» := P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
