-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_half_gen
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.half_gen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:18.397726+00:00
-- url     : https://prove2.me/theorems/266ffaa0-6631-463c-8f85-41f975f64b7c
-- title:
--   Gen: half gen
-- statement:
--   The Gen construction uses the half gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateEqTG.lean#L40-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateEqTG.lean#L40-L66

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

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.half_gen [Algebra ℚ k] [Fintype ι]
    (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
    (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
    (e : S →+* k) (he : ∀ a, e (κ a) = a) (c : ι → ι → k) (q : S) (hc : ∀ l l', c l l' = c l' l)
    (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
    (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P (A * q)) = algebraMap ℚ k (1 / 2) * e (PolG D κ (secondOrder k c P) A) := by sorry
