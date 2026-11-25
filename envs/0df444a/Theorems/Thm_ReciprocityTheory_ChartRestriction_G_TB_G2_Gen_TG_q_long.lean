-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_TG_q_long
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_q_long
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:33.512696+00:00
-- url     : https://prove2.me/theorems/6d547513-eaa9-51b8-a3c6-9aa12f2f40d9
-- title:
--   Gen: TG q long
-- statement:
--   The Gen construction uses the TG q long property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ETGMulQ.lean#L55-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ETGMulQ.lean#L55-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2 ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
open ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
include hadd hC hq2

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_q_long (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by sorry
