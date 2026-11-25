-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_mul_inv_mul_7a54f0c5aaed
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_mul_inv_mul_7a54f0c5aaed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:17.394124+00:00
-- url     : https://prove2.me/theorems/e55b61d4-72f0-58cd-ab3a-f9e964d59378
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume majorant mul inv mul 7a54f0c5aaed: P2 M Ground Theory Heights  Heights Finite Covolume majorant mul inv mul 7a54f0c5aaed
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume majorant mul inv mul 7a54f0c5aaed construction uses the P2 M Ground Theory Heights  Heights Finite Covolume majorant mul inv mul 7a54f0c5aaed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantBound.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantBound.lean#L9-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
open scoped ComplexOrder

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_mul_inv_mul_7a54f0c5aaed {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) : H * P⁻¹ * H = P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«majorant_mul_inv_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_majorant_mul_inv_mul_7a54f0c5aaed
