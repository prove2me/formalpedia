-- Prove2me | Theorems.Thm_P2M_UnipMove_herm_smul_left__6f6c7a1bcd4e
-- name    : P2M_UnipMove_herm_smul_left__6f6c7a1bcd4e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:32.272107+00:00
-- url     : https://prove2.me/theorems/ca4c2f71-4f60-4ebf-a59b-e2eff827c8a4
-- title:
--   P2 M Unip Move herm smul left  6f6c7a1bcd4e: P2 M Unip Move herm smul left  6f6c7a1bcd4e
-- statement:
--   The P2 M Unip Move herm smul left  6f6c7a1bcd4e construction uses the P2 M Unip Move herm smul left  6f6c7a1bcd4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermSmulLeft.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/UnipotentMoves/HermSmulLeft.lean#L10-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermSmulLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem P2M_UnipMove_herm_smul_left__6f6c7a1bcd4e {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by sorry

alias «UnipMove».«herm_smul_left'» := P2M_UnipMove_herm_smul_left__6f6c7a1bcd4e
