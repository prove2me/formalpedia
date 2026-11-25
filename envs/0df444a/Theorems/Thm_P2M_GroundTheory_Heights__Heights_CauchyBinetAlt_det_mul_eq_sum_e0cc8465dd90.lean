-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_mul_eq_sum_e0cc8465dd90
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_mul_eq_sum_e0cc8465dd90
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:01.068912+00:00
-- url     : https://prove2.me/theorems/717de03f-b296-41ee-b5bc-408f6fb6ae25
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Alt det mul eq sum e0cc8465dd90: P2 M Ground Theory Heights  Heights Cauchy Binet Alt det mul eq sum e0cc8465dd90
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Alt det mul eq sum e0cc8465dd90 construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Alt det mul eq sum e0cc8465dd90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
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
open Matrix Finset Equiv
open GroundTheory.Heights₂.Heights.CauchyBinetAlt
variable {R : Type*} [CommRing R] {j N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_mul_eq_sum_e0cc8465dd90 (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R) :
    (A * B).det = ∑ p : Fin j → Fin N, (∏ i, B (p i) i) * (A.submatrix id p).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetAlt».«det_mul_eq_sum» := P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_mul_eq_sum_e0cc8465dd90
