-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_span_basis_formNorm_le_4126249bc729
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_span_basis_formNorm_le_4126249bc729
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:38.481639+00:00
-- url     : https://prove2.me/theorems/bb303c6c-0ef1-44fb-88d0-96b23f89e22d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout span basis form Norm le 4126249bc729: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout sp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout span basis form Norm le 4126249bc729 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Arith Bezout span basis form Norm le 4126249bc729 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L322-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SpecFirstDetFormNeZero.lean#L322-L339

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LatticePointLogCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_span_basis_formNorm_le_4126249bc729 (n : ℕ) :
    ∃ G : Set (Fin n → ℤ), Submodule.span ℤ G = ⊤ ∧
      ∀ u ∈ G, formNorm (1 : Matrix (Fin n) (Fin n) ℂ) (fun i => (u i : ℂ)) ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ArithBezout».«span_basis_formNorm_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ArithBezout_span_basis_formNorm_le_4126249bc729
