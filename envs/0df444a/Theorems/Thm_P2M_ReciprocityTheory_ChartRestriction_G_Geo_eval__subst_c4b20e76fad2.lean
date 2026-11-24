-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_eval__subst_c4b20e76fad2
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Geo_eval__subst_c4b20e76fad2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:36.159016+00:00
-- url     : https://prove2.me/theorems/645f69cd-50cb-4c0f-adc7-2f36aeee1427
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Geo eval  subst c4b20e76fad2: P2 M Reciprocity Theory Chart Restriction G Geo eval  subst c4b20e76fad2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Geo eval  subst c4b20e76fad2 construction uses the P2 M Reciprocity Theory Chart Restriction G Geo eval  subst c4b20e76fad2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L108-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean#L108-L123

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Geo_eval__subst_c4b20e76fad2 {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (lam : Fin r → k)
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) :
    Polynomial.eval₂ ((aeval (fun i => ℓ i.succ - lam i • ℓ 0) : MvPolynomial (Fin r) k →ₐ[k] R) :
      MvPolynomial (Fin r) k →+* R) (ℓ 0) (subst lam F) =
      aeval ℓ F := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Geo».«eval₂_subst» := P2M_ReciprocityTheory_ChartRestriction_G_Geo_eval__subst_c4b20e76fad2
