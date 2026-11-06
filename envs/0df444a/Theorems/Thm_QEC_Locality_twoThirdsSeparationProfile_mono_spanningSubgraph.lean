-- Prove2me | Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_mono_spanningSubgraph
-- name    : QEC.Locality.twoThirdsSeparationProfile_mono_spanningSubgraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:14:39.012211+00:00
-- url     : https://prove2.me/theorems/dcc6853f-5202-475a-a80e-7dfc91d703e9
-- title:
--   Locality: two Thirds Separation Profile mono spanning Subgraph
-- statement:
--   The exact induced-subgraph separation profile is monotone under edge deletion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L61-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/EdgeDivision.lean#L61-L73

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.twoThirdsSeparationProfile_mono_spanningSubgraph
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G) (scale : Nat) :
    twoThirdsSeparationProfile H scale ≤ twoThirdsSeparationProfile G scale := by sorry
