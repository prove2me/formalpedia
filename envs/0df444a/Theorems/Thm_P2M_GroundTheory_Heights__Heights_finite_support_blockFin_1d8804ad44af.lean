-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af
-- name    : P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.744076+00:00
-- url     : https://prove2.me/theorems/d1e7979f-cb5d-4671-901e-c674e43a8267
-- title:
--   P2 M Ground Theory Heights  Heights finite support block Fin 1d8804ad44af: P2 M Ground Theory Heights  Heights finite support block Fin 1d8804ad44af
-- statement:
--   The P2 M Ground Theory Heights  Heights finite support block Fin 1d8804ad44af construction uses the P2 M Ground Theory Heights  Heights finite support block Fin 1d8804ad44af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L104-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L104-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Field K] [NumberField K]
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af (y : Cone n K) (k : ι) (hy : y k ≠ 0) :
    (Function.support (blockFin y k)).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finite_support_blockFin» := P2M_GroundTheory_Heights__Heights_finite_support_blockFin_1d8804ad44af
