-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_pos_of_hasEdge
-- name    : QEC.Locality.twoThirdsSeparationProfile_pos_of_hasEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:30:47.115539+00:00
-- url     : https://prove2.me/theorems/3382dd49-ff23-4ec5-b58e-9eeee7d9c4a2
-- title:
--   Locality: two Thirds Separation Profile pos of has Edge
-- statement:
--   An actual graph edge forces the measured `2/3` separation profile to be
--   positive at every scale at least two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L42-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/MaxFamily.lean#L42-L109

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u v

theorem QEC.Locality.twoThirdsSeparationProfile_pos_of_hasEdge
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (hEdge : G.HasEdge) {scale : Nat}
    (hscale : 2 ≤ scale) :
    0 < twoThirdsSeparationProfile G scale := by sorry
