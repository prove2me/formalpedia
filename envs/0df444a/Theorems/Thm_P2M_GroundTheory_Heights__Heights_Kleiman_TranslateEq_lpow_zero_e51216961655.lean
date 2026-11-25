-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_zero_e51216961655
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_zero_e51216961655
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:42.857841+00:00
-- url     : https://prove2.me/theorems/92d3334b-5c8c-4e47-99d9-28ba9f7e1be2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq lpow zero e51216961655: P2 M Ground Theory Heights  Heights Kleiman Translate Eq lpow zero e51216961655
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq lpow zero e51216961655 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq lpow zero e51216961655 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L350-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L350-L351

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_zero_e51216961655 (Q : Fin (N + 1) → Submodule S Ω) (i : Fin (N + 1)) : IndefiniteRowSideFullHecke.Kleiman.lpow S Q 0 i = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«lpow_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lpow_zero_e51216961655
