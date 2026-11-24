-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:52.82721+00:00
-- url     : https://prove2.me/theorems/a7ddac16-2cd9-4eb9-9422-6c95cdea232c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs equiv 51d02eb19002: P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs equiv 51d02eb19002
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs equiv 51d02eb19002 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq secs equiv 51d02eb19002 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L158-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L158-L174

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002 (F : Kleiman.SubSystem S x E) : IndefiniteRowSideFullHecke.Kleiman.secs S x (toIndefiniteRowSideFullHecke F) = F.secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«secs».«equiv» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
