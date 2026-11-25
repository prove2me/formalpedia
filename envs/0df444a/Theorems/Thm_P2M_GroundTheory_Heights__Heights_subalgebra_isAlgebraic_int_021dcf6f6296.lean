-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_subalgebra_isAlgebraic_int_021dcf6f6296
-- name    : P2M_GroundTheory_Heights__Heights_subalgebra_isAlgebraic_int_021dcf6f6296
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:27.40996+00:00
-- url     : https://prove2.me/theorems/c982419e-64f6-436d-bcc1-62894a8e4e90
-- title:
--   P2 M Ground Theory Heights  Heights subalgebra is Algebraic int 021dcf6f6296: P2 M Ground Theory Heights  Heights subalgebra is Algebraic int 021dcf6f6296
-- statement:
--   The P2 M Ground Theory Heights  Heights subalgebra is Algebraic int 021dcf6f6296 construction uses the P2 M Ground Theory Heights  Heights subalgebra is Algebraic int 021dcf6f6296 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PSubringPrimeMaximal.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PSubringPrimeMaximal.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
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
open NumberField Polynomial

theorem P2M_GroundTheory_Heights__Heights_subalgebra_isAlgebraic_int_021dcf6f6296 {K : Type} [Field K] [NumberField K] (O : Subalgebra ℤ K)
    (y : O) : IsAlgebraic ℤ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«subalgebra_isAlgebraic_int» := P2M_GroundTheory_Heights__Heights_subalgebra_isAlgebraic_int_021dcf6f6296
