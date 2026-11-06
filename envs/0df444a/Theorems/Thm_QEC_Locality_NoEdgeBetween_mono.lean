-- Prove2me | Theorems.Thm_QEC_Locality_NoEdgeBetween_mono
-- name    : QEC.Locality.NoEdgeBetween.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:52.208199+00:00
-- url     : https://prove2.me/theorems/233d91f7-fe65-46c5-a5c0-4e9cd424e849
-- title:
--   No Edge Between: mono
-- statement:
--   The No Edge Between construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L258-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L258-L263

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.NoEdgeBetween.mono {G : ConnectivityGraph ι}
    {left right left' right' : Finset ι}
    (h : NoEdgeBetween G left right) (hleft : left' ⊆ left) (hright : right' ⊆ right) :
    NoEdgeBetween G left' right' := by sorry
