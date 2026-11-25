-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_det_rev_pow_eq_vandermondeOf_025293c6ef5f
-- name    : P2M_GroundTheory_Heights__Heights_KRest_det_rev_pow_eq_vandermondeOf_025293c6ef5f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:23.193947+00:00
-- url     : https://prove2.me/theorems/02c78bc9-fcbd-45f7-ba84-7e4f87a0fa57
-- title:
--   P2 M Ground Theory Heights  Heights KRest det rev pow eq vandermonde Of 025293c6ef5f: P2 M Ground Theory Heights  Heights KRest det rev pow eq vandermonde Of 025293c6ef5f
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest det rev pow eq vandermonde Of 025293c6ef5f construction uses the P2 M Ground Theory Heights  Heights KRest det rev pow eq vandermonde Of 025293c6ef5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L48-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_det_rev_pow_eq_vandermondeOf_025293c6ef5f {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det = RestTerms.vandermondeOf v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«det_rev_pow_eq_vandermondeOf» := P2M_GroundTheory_Heights__Heights_KRest_det_rev_pow_eq_vandermondeOf_025293c6ef5f
