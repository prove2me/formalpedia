-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:22:41.7338+00:00
-- url     : https://prove2.me/theorems/f1ffb61b-0321-42d6-8f90-2b1d906554f1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Translate Eq span image2 eq 67f8a4da0bc8: P2 M Ground Theory Heights  Heights Kleiman Translate Eq span image2 eq 67f8a4da0bc8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Translate Eq span image2 eq 67f8a4da0bc8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Translate Eq span image2 eq 67f8a4da0bc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L231-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/EqZeroOrIsHomogeneousOfMemPolyPiece.lean#L231-L254

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8 (A : Subalgebra S Ω) (T : Set E) :
    Submodule.span S (Set.image2 (· • ·) (A : Set Ω) T) = (Submodule.span A T).restrictScalars S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TranslateEq».«span_image2_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8
