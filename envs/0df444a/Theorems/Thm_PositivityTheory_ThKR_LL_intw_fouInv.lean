-- Prove2me | Theorems.Thm_PositivityTheory_ThKR_LL_intw_fouInv
-- name    : PositivityTheory.ThKR.LL.intw_fouInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:19.588405+00:00
-- url     : https://prove2.me/theorems/aea1c8cd-b30b-42fd-9b7c-c7cfddb54b05
-- title:
--   LL: intw fou Inv
-- statement:
--   The LL construction uses the intw fou Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/IsoOfIntegral.lean#L169-L174

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem PositivityTheory.ThKR.LL.intw_fouInv (p q : Eu l) : Intw (fouInv l) p q q (-p) := by sorry
