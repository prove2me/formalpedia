-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_submatrix_eq_zero_cec33daaf8a4
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_submatrix_eq_zero_cec33daaf8a4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:58.372146+00:00
-- url     : https://prove2.me/theorems/de74f703-b45e-4f2b-b169-e401cebcc4f9
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Alt det submatrix eq zero cec33daaf8a4: P2 M Ground Theory Heights  Heights Cauchy Binet Alt det submatrix eq zero cec33daaf8a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Alt det submatrix eq zero cec33daaf8a4 construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Alt det submatrix eq zero cec33daaf8a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_submatrix_eq_zero_cec33daaf8a4 (A : Matrix (Fin j) (Fin N) R) {p : Fin j → Fin N}
    (hp : ¬ Function.Injective p) : (A.submatrix id p).det = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetAlt».«det_submatrix_eq_zero» := P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_det_submatrix_eq_zero_cec33daaf8a4
