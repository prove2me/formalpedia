-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_ds_relIndex_span_comb
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.ds_relIndex_span_comb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:53:08.828983+00:00
-- url     : https://prove2.me/theorems/5dea8197-ff65-53a4-a426-4378e5b8c3be
-- title:
--   Geometry Of Numbers Theory: ds rel Index span comb
-- statement:
--   The Geometry Of Numbers Theory construction uses the ds rel Index span comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean#L11-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/DegStB.lean#L11-L73

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB
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

theorem ReciprocityTheory.GeometryOfNumbersTheory.ds_relIndex_span_comb {r : ℕ} {v : Fin r → V} (hv : LinearIndependent K v)
    (g : Matrix (Fin r) (Fin r) (𝓞 K)) (hg : g.det ≠ 0) :
    (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = (Algebra.norm ℤ g.det).natAbs := by sorry
