-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_isHomogeneous_vandermondeOf_c370fdda67bb
-- name    : P2M_GroundTheory_Heights__Heights_KRest_isHomogeneous_vandermondeOf_c370fdda67bb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:01.383794+00:00
-- url     : https://prove2.me/theorems/f8d06a79-bd78-4b4b-863e-a17b595b9c9b
-- title:
--   P2 M Ground Theory Heights  Heights KRest is Homogeneous vandermonde Of c370fdda67bb: P2 M Ground Theory Heights  Heights KRest is Homogeneous vandermonde Of c370fdda67bb
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest is Homogeneous vandermonde Of c370fdda67bb construction uses the P2 M Ground Theory Heights  Heights KRest is Homogeneous vandermonde Of c370fdda67bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutRestHom.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutRestHom.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutRestHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.KRest

theorem P2M_GroundTheory_Heights__Heights_KRest_isHomogeneous_vandermondeOf_c370fdda67bb {σ R : Type*} [CommRing R] {m : ℕ}
    (v : Fin m → MvPolynomial σ R) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (RestTerms.vandermondeOf v).IsHomogeneous (∑ i : Fin m, (Finset.Ioi i).card) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«isHomogeneous_vandermondeOf» := P2M_GroundTheory_Heights__Heights_KRest_isHomogeneous_vandermondeOf_c370fdda67bb
