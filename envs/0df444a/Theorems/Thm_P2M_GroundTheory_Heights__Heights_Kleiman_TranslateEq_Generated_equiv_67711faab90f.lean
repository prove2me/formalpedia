-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:03.867092+00:00
-- url     : https://prove2.me/theorems/d7c560df-c159-4df8-a766-0925340985b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq Generated equiv 67711faab90f: P2 M Ground Theory Heights  Heights Kleiman Translate Eq Generated equiv 67711faab90f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq Generated equiv 67711faab90f construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq Generated equiv 67711faab90f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L256-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L256-L304

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f (F : Kleiman.SubFamily S x E) :
    IndefiniteRowSideFullHecke.Kleiman.IsGenerated S x (toIndefiniteRowSideFullHecke F.toSubSystem) ↔ F.toSubSystem.Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«Generated».«equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f
