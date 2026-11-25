-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_elt_div_elt_eac7066069af
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockData_elt_div_elt_eac7066069af
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:37.447642+00:00
-- url     : https://prove2.me/theorems/3722ed92-2471-4a71-b05f-9d9ea78c58f7
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Data elt div elt eac7066069af: P2 M Ground Theory Heights  Heights Add Block Data elt div elt eac7066069af
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Data elt div elt eac7066069af construction uses the P2 M Ground Theory Heights  Heights Add Block Data elt div elt eac7066069af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartPowNeZero.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/ChartPowNeZero.lean#L19-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
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
open GroundTheory.Heights₂.Heights.AddBlockData
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)

theorem P2M_GroundTheory_Heights__Heights_AddBlockData_elt_div_elt_eac7066069af {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (i j : Fin (D.size + 1)) :
    D.elt i / D.elt j = D.xi c i * (D.xi c j)⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockData».«elt_div_elt» := P2M_GroundTheory_Heights__Heights_AddBlockData_elt_div_elt_eac7066069af
