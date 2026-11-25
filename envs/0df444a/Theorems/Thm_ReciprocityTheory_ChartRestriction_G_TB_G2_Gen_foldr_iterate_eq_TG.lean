-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_foldr_iterate_eq_TG
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.foldr_iterate_eq_TG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:27.005488+00:00
-- url     : https://prove2.me/theorems/615b5ef6-6273-4ec8-bf7a-d5258a1e7df9
-- title:
--   Gen: foldr iterate eq TG
-- statement:
--   The Gen construction uses the foldr iterate eq TG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateEqTG.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateEqTG.lean#L25-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
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

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.foldr_iterate_eq_TG (Ls : List ι) (m : ι →₀ ℕ) (A : S) :
    Ls.foldr (fun l g => (D l)^[m l] g) A = TG D (word Ls m) A := by sorry
