-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_topologicalKrullDim_eq_of_isIso_restrict__b00c8800f9d8
-- name    : P2M_GlobalTheory_T_topologicalKrullDim_eq_of_isIso_restrict__b00c8800f9d8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:07:10.538404+00:00
-- url     : https://prove2.me/theorems/d3dc4c9e-f7a2-4e9d-bdb3-8e22910eeb91
-- title:
--   P2 M Global Theory T topological Krull Dim eq of is Iso restrict  b00c8800f9d8: P2 M Global Theory T topological Krull Dim eq of is Iso restrict  b00c8800f9d8
-- statement:
--   The P2 M Global Theory T topological Krull Dim eq of is Iso restrict  b00c8800f9d8 construction uses the P2 M Global Theory T topological Krull Dim eq of is Iso restrict  b00c8800f9d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrictStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimEqOfIsIsoRestrictStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrict
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimEqOfIsIsoRestrictStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_topologicalKrullDim_eq_of_isIso_restrict__b00c8800f9d8 : ∀ (F : Type) [Field F] (W W' : Scheme.{0}) [IsIntegral W] [IsIntegral W'] (p : W ⟶ Sp F) (q : W' ⟶ Sp F) (h : W' ⟶ W), LocallyOfFiniteType p → LocallyOfFiniteType q → h ≫ p = q → ∀ U : W.Opens, (U : Set W).Nonempty → IsIso (h ∣_ U) → topologicalKrullDim W' = topologicalKrullDim W := by sorry

alias «GlobalTheory».«T».«topologicalKrullDim_eq_of_isIso_restrict'» := P2M_GlobalTheory_T_topologicalKrullDim_eq_of_isIso_restrict__b00c8800f9d8
