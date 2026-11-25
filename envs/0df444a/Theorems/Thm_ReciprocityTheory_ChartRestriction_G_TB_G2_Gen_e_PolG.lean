-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_e_PolG
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.e_PolG
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:48.916926+00:00
-- url     : https://prove2.me/theorems/c2c061e2-c8ef-40a7-93d3-488a4ffa8437
-- title:
--   Gen: e Pol G
-- statement:
--   The Gen construction uses the e Pol G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateEqTG.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateEqTG.lean#L34-L38

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

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.e_PolG [Fintype ι] (e : S →+* k) (he : ∀ a, e (κ a) = a) (P : MvPolynomial ι k) (A : S) :
    e (PolG D κ P A) = (AddMonoidAlgebra.coeff P).sum
      (fun n a => a * e (TG D (word (Finset.univ : Finset ι).toList n) A)) := by sorry
