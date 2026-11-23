-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_conn_int_rat_bijective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.conn_int_rat_bijective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:15.424981+00:00
-- url     : https://prove2.me/theorems/e9259ae9-cc24-4975-8c45-bc873ebc578e
-- title:
--   Local Class Field: conn int rat bijective
-- statement:
--   The Local Class Field construction uses the conn int rat bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L69-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HSubsingletonOfUniquelyDivisible.lean#L69-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemZmultiplesOfAddOrderOf
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
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
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.conn_int_rat_bijective [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (δ : ∀ n, (trivRep G QZ).H n →ₗ[ℤ] (trivRep G ℤ).H (n + 1))
    (hδ : Cx.IsConn (trivMap G (Int.castAddHom ℚ)).hom
      (trivMap G (QuotientAddGroup.mk' (Int.castAddHom ℚ).range)).hom δ) (n : ℕ) (hn : 0 < n) :
    Bijective (δ n) := by sorry
