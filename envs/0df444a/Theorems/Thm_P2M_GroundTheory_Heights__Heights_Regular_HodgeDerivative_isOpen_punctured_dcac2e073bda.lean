-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_isOpen_punctured_dcac2e073bda
-- name    : P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_isOpen_punctured_dcac2e073bda
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:13.824096+00:00
-- url     : https://prove2.me/theorems/9784e319-3c63-46dc-93d5-4a16a0846a47
-- title:
--   P2 M Ground Theory Heights  Heights Regular Hodge Derivative is Open punctured dcac2e073bda: P2 M Ground Theory Heights  Heights Regular Hodge Derivative is Open punctured dcac2e073bda
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Hodge Derivative is Open punctured dcac2e073bda construction uses the P2 M Ground Theory Heights  Heights Regular Hodge Derivative is Open punctured dcac2e073bda property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PHodgeDerivative.lean#L21-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative

theorem P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_isOpen_punctured_dcac2e073bda {n a : ℕ} (h : a ≤ n) :
    IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«HodgeDerivative».«isOpen_punctured» := P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_isOpen_punctured_dcac2e073bda
