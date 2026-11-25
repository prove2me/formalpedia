-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_kaehler_D_aeval_da53b3b7fe57
-- name    : P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_kaehler_D_aeval_da53b3b7fe57
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:05.814276+00:00
-- url     : https://prove2.me/theorems/a958fbc9-fac5-4fce-affe-b06849157652
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian Rank Generic kaehler D aeval da53b3b7fe57: P2 M Ground Theory Heights  Heights Jacobian Rank Generic kaehler D aeval da53b3b7fe57
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian Rank Generic kaehler D aeval da53b3b7fe57 construction uses the P2 M Ground Theory Heights  Heights Jacobian Rank Generic kaehler D aeval da53b3b7fe57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PJacobianRankGeneric.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PJacobianRankGeneric.lean#L12-L24

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
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
noncomputable section
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_kaehler_D_aeval_da53b3b7fe57 {σ K : Type*} [Fintype σ] [Field K] [Algebra ℂ K] (x : σ → K)
    (f : MvPolynomial σ ℂ) :
    KaehlerDifferential.D ℂ K (aeval x f) =
      ∑ l, aeval x (pderiv l f) • KaehlerDifferential.D ℂ K (x l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianRankGeneric».«kaehler_D_aeval» := P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_kaehler_D_aeval_da53b3b7fe57
