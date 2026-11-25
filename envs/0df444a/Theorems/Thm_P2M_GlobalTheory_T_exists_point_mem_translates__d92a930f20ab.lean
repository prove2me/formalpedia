-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_point_mem_translates__d92a930f20ab
-- name    : P2M_GlobalTheory_T_exists_point_mem_translates__d92a930f20ab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:32.336798+00:00
-- url     : https://prove2.me/theorems/cec47dbf-a491-555c-a6fb-7705607cdb78
-- title:
--   P2 M Global Theory T exists point mem translates  d92a930f20ab: P2 M Global Theory T exists point mem translates  d92a930f20ab
-- statement:
--   The P2 M Global Theory T exists point mem translates  d92a930f20ab construction uses the P2 M Global Theory T exists point mem translates  d92a930f20ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPointMemTranslatesStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPointMemTranslatesStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPointMemTranslates
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPointMemTranslatesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_point_mem_translates__d92a930f20ab : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens), (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)), ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧ (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by sorry

alias «GlobalTheory».«T».«exists_point_mem_translates'» := P2M_GlobalTheory_T_exists_point_mem_translates__d92a930f20ab
