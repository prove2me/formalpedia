-- Prove2me | Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
-- name    : QEC.Locality.NoEdgeBetween.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:42.243086+00:00
-- url     : https://prove2.me/theorems/4da2650e-cc57-4ff7-9ab7-3a60cd47da21
-- title:
--   No Edge Between: symm
-- statement:
--   The No Edge Between construction uses the symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L265-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L265-L268

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

theorem QEC.Locality.NoEdgeBetween.symm {G : ConnectivityGraph ι} {left right : Finset ι}
    (h : NoEdgeBetween G left right) : NoEdgeBetween G right left := by sorry
