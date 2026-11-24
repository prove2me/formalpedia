-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867
-- name    : P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:49.032743+00:00
-- url     : https://prove2.me/theorems/3eb1e9ca-7988-41cc-a16d-b88a84e758c8
-- title:
--   P2 M Ground Theory Heights  Heights sum weight Set component 481e5721c867: P2 M Ground Theory Heights  Heights sum weight Set component 481e5721c867
-- statement:
--   The P2 M Ground Theory Heights  Heights sum weight Set component 481e5721c867 construction uses the P2 M Ground Theory Heights  Heights sum weight Set component 481e5721c867 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L18-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
noncomputable section
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}

theorem P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867 (p : MvPolynomial σ R) :
    ∑ a ∈ weightSet w p, weightedHomogeneousComponent w a p = p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sum_weightSet_component» := P2M_GroundTheory_Heights__Heights_sum_weightSet_component_481e5721c867
