-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_ptsIntegral_eq_mInt__6df43e64201d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_ptsIntegral_eq_mInt__6df43e64201d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:02.372816+00:00
-- url     : https://prove2.me/theorems/157ff1db-51eb-4e4d-ae48-bb28f25b7f8c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo pts Integral eq m Int  6df43e64201d: P2 M Reciprocity Theory Chart Restriction G Geo pts Integral eq m Int  6df43e64201d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo pts Integral eq m Int  6df43e64201d construction uses the P2 M Reciprocity Theory Chart Restriction G Geo pts Integral eq m Int  6df43e64201d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedE.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedE.lean#L8-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_ptsIntegral_eq_mInt__6df43e64201d (hE : ResExistsStatement) (hB : ResBridgeStatement) {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) =
      ReciprocityTheory.AnForm.M.mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«ptsIntegral_eq_mInt'» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_ptsIntegral_eq_mInt__6df43e64201d
