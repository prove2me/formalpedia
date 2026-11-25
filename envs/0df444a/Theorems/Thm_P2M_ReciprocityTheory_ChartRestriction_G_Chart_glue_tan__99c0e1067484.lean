-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan__99c0e1067484
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan__99c0e1067484
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:00.107262+00:00
-- url     : https://prove2.me/theorems/6bb9ba65-dd33-4428-b3b5-0818dbbbb388
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Chart glue tan  99c0e1067484: P2 M Reciprocity Theory Chart Restriction G Chart glue tan  99c0e1067484
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Chart glue tan  99c0e1067484 construction uses the P2 M Reciprocity Theory Chart Restriction G Chart glue tan  99c0e1067484 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L135-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L135-L197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan__99c0e1067484 {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Chart».«glue_tan'» := P2M_ReciprocityTheory_ChartRestriction_G_Chart_glue_tan__99c0e1067484
