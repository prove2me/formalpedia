-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twistA_iff_917ff1481aae
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twistA_iff_917ff1481aae
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:48.531582+00:00
-- url     : https://prove2.me/theorems/fa59a55a-9087-4ca4-a32e-d13a9941946e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist A iff 917ff1481aae: P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist A iff 917ff1481aae
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist A iff 917ff1481aae construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq mem twist A iff 917ff1481aae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L176-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L176-L191

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twistA_iff_917ff1481aae (F : Fin (N + 1) → Submodule S E) (c : ℤ) (i : Fin (N + 1)) (z : E) :
    z ∈ IndefiniteRowSideFullHecke.Kleiman.twistA S x F c i ↔ ∃ y ∈ F i, z = x i ^ c • y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«mem_twistA_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twistA_iff_917ff1481aae
