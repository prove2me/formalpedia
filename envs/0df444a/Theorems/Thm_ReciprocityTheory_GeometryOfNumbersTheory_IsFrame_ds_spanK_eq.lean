-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_ds_spanK_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.ds_spanK_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:47.832349+00:00
-- url     : https://prove2.me/theorems/925fbe67-63cc-4aeb-9841-09e70d1963c3
-- title:
--   Is Frame: ds span K eq
-- statement:
--   The Is Frame construction uses the ds span K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStA.lean#L11-L15

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.ds_spanK_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span K (Set.range v) = Submodule.span K (E : Set V) := by sorry
