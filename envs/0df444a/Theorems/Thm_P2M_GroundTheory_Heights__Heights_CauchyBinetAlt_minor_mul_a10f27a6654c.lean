-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_minor_mul_a10f27a6654c
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_minor_mul_a10f27a6654c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:14.794034+00:00
-- url     : https://prove2.me/theorems/9314efc5-a70b-48a0-8809-c13caa976caf
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Alt minor mul a10f27a6654c: P2 M Ground Theory Heights  Heights Cauchy Binet Alt minor mul a10f27a6654c
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Alt minor mul a10f27a6654c construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Alt minor mul a10f27a6654c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L28-L40

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

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_minor_mul_a10f27a6654c (A : Matrix (Fin j) (Fin N) R) (B : Matrix (Fin N) (Fin j) R)
    (I : {I : Finset (Fin N) // I.card = j}) :
    (colsOf A I).det * (rowsOf B I).det =
      ∑ w : Perm (Fin j), (∏ i, B (I.1.orderEmbOfFin I.2 (w i)) i) *
        (A.submatrix id (I.1.orderEmbOfFin I.2 ∘ w)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetAlt».«minor_mul» := P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_minor_mul_a10f27a6654c
