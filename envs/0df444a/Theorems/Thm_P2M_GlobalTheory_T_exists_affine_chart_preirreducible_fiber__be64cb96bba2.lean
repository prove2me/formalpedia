-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_affine_chart_preirreducible_fiber__be64cb96bba2
-- name    : P2M_GlobalTheory_T_exists_affine_chart_preirreducible_fiber__be64cb96bba2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:09.052242+00:00
-- url     : https://prove2.me/theorems/98804c5d-8891-4800-a397-ffc93a429965
-- title:
--   P2 M Global Theory T exists affine chart preirreducible fiber  be64cb96bba2: P2 M Global Theory T exists affine chart preirreducible fiber  be64cb96bba2
-- statement:
--   The P2 M Global Theory T exists affine chart preirreducible fiber  be64cb96bba2 construction uses the P2 M Global Theory T exists affine chart preirreducible fiber  be64cb96bba2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineChartPreirreducibleFiberStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineChartPreirreducibleFiberStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiberStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_affine_chart_preirreducible_fiber__be64cb96bba2 : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by sorry

alias «GlobalTheory».«T».«exists_affine_chart_preirreducible_fiber'» := P2M_GlobalTheory_T_exists_affine_chart_preirreducible_fiber__be64cb96bba2
