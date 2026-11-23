-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497
-- name    : P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:26.405723+00:00
-- url     : https://prove2.me/theorems/4f31e76f-0c5e-4b8d-9b55-1e3951b09beb
-- title:
--   P2 M Ground Theory Heights  Heights MCDet det eq of Real re ede617190497: P2 M Ground Theory Heights  Heights MCDet det eq of Real re ede617190497
-- statement:
--   The P2 M Ground Theory Heights  Heights MCDet det eq of Real re ede617190497 construction uses the P2 M Ground Theory Heights  Heights MCDet det eq of Real re ede617190497 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean#L12-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497 {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.det = (RCLike.re A.det : 𝕜) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCDet».«det_eq_ofReal_re» := P2M_GroundTheory_Heights__Heights_MCDet_det_eq_ofReal_re_ede617190497
