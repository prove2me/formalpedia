-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_TG_mul
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:28.290782+00:00
-- url     : https://prove2.me/theorems/5be8021f-44c8-59bc-9b19-ee346e9a736a
-- title:
--   Gen: TG mul
-- statement:
--   The Gen construction uses the TG mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ETGMulQ.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ETGMulQ.lean#L40-L48

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
include hadd hmul

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_mul (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by sorry
