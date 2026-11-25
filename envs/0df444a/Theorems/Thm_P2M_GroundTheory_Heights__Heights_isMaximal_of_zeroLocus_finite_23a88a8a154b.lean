-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMaximal_of_zeroLocus_finite_23a88a8a154b
-- name    : P2M_GroundTheory_Heights__Heights_isMaximal_of_zeroLocus_finite_23a88a8a154b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:25.761668+00:00
-- url     : https://prove2.me/theorems/4bf05555-449d-4ffb-aea9-be7a5de2f798
-- title:
--   P2 M Ground Theory Heights  Heights is Maximal of zero Locus finite 23a88a8a154b: P2 M Ground Theory Heights  Heights is Maximal of zero Locus finite 23a88a8a154b
-- statement:
--   The P2 M Ground Theory Heights  Heights is Maximal of zero Locus finite 23a88a8a154b construction uses the P2 M Ground Theory Heights  Heights is Maximal of zero Locus finite 23a88a8a154b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFiniteFibresDimLe.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFiniteFibresDimLe.lean#L12-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMaximalIdealHeightFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFiniteFibresDimLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_isMaximal_of_zeroLocus_finite_23a88a8a154b {n : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [hP : P.IsPrime]
    (hfin : (zeroLocus ℂ P : Set (Fin n → ℂ)).Finite) : P.IsMaximal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isMaximal_of_zeroLocus_finite» := P2M_GroundTheory_Heights__Heights_isMaximal_of_zeroLocus_finite_23a88a8a154b
