-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:03.871722+00:00
-- url     : https://prove2.me/theorems/6f96a0cb-b0fe-4619-a79d-fce44edc4297
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist equiv 61178bbb85a9: P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist equiv 61178bbb85a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist equiv 61178bbb85a9 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq twist equiv 61178bbb85a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L224-L229

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9 (F : Kleiman.SubSystem S x E) (c : ℤ) {i : Fin (N + 1)} (h : x i ≠ 0) :
    IndefiniteRowSideFullHecke.Kleiman.twistA S x (toIndefiniteRowSideFullHecke F) c i = toIndefiniteRowSideFullHecke (F.twist (Kleiman.twistSys S x c)) i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«twist».«equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
