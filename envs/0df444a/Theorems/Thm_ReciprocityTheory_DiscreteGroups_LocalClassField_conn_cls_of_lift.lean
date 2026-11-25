-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_conn_cls_of_lift
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.conn_cls_of_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:25.881623+00:00
-- url     : https://prove2.me/theorems/c0ee9808-eafb-4482-b4e9-6a33d95f6134
-- title:
--   Local Class Field: conn cls of lift
-- statement:
--   The Local Class Field construction uses the conn cls of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L162-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean#L162-L194

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.conn_cls_of_lift (δ)
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ)
    (t : G → ℚ) (ht : IsLocallyConstant t) (m : (Fin 2 → G) → ℤ)
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (x : (trivRep G QZ).coch.X 1) (hx : (trivRep G QZ).coch.d 1 x = 0) (y : (trivRep G ℤ).coch.X 2)
      (hy : (trivRep G ℤ).coch.d 2 y = 0), (∀ g, x.1 g = (QuotientAddGroup.mk (t (g 0)) : QZ)) ∧ y.1 = m ∧
      δ 1 ((trivRep G QZ).coch.cls 1 x hx) = (trivRep G ℤ).coch.cls 2 y hy := by sorry
