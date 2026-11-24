-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:09.464395+00:00
-- url     : https://prove2.me/theorems/b7620ade-4678-432a-950c-5a3e6d21700c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq chart Module of ne zero 902c51d3fd20: P2 M Ground Theory Heights  Heights Kleiman Translate Eq chart Module of ne zero 902c51d3fd20
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq chart Module of ne zero 902c51d3fd20 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq chart Module of ne zero 902c51d3fd20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L154-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20 (F : Kleiman.SubSystem S x E) {i : Fin (N + 1)} (h : x i ≠ 0) :
    toIndefiniteRowSideFullHecke F i = (F.sub (Kleiman.singleChart h)).restrictScalars S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«chartModule_of_ne_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
