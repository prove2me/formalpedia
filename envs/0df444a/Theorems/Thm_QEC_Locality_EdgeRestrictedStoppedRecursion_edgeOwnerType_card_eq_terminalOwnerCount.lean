-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeOwnerType_card_eq_terminalOwnerCount
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.edgeOwnerType_card_eq_terminalOwnerCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:15.549095+00:00
-- url     : https://prove2.me/theorems/0d023159-3a0a-44d0-a326-844417eb5fa5
-- title:
--   Edge Restricted Stopped Recursion: edge Owner Type card eq terminal Owner Count
-- statement:
--   The Edge Restricted Stopped Recursion construction uses the edge Owner Type card eq terminal Owner Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L339-L348
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L339-L348

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.edgeOwnerType_card_eq_terminalOwnerCount
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    Fintype.card tree.edgeOwnerType = tree.terminalOwnerCount := by sorry
