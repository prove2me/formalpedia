-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:31.078436+00:00
-- url     : https://prove2.me/theorems/4e3a6c14-0fe7-4813-a94c-1c548a68988f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow zero sub b7a88b6ce0bd: P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow zero sub b7a88b6ce0bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow zero sub b7a88b6ce0bd construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq pow zero sub b7a88b6ce0bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L353-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L353-L363

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd (Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) (z : Ω) :
    z ∈ (Q.pow 0).sub I ↔ z ∈ Kleiman.chartRing S x I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«pow_zero_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_pow_zero_sub_b7a88b6ce0bd
