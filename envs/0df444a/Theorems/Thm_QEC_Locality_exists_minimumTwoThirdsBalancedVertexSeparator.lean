-- Prove2me | Theorems.Thm_QEC_Locality_exists_minimumTwoThirdsBalancedVertexSeparator
-- name    : QEC.Locality.exists_minimumTwoThirdsBalancedVertexSeparator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:49:52.738193+00:00
-- url     : https://prove2.me/theorems/36269aac-5183-4347-a230-2908ed183f63
-- title:
--   Locality: exists minimum Two Thirds Balanced Vertex Separator
-- statement:
--   The measured minimum is witnessed by an explicit finite separator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L60-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Core.lean#L60-L73

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
set_option autoImplicit false
open QEC QEC.Locality
universe u

theorem QEC.Locality.exists_minimumTwoThirdsBalancedVertexSeparator {ι : Type u} [Fintype ι] [DecidableEq ι]
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    ∃ separator : Finset ι,
      separator ⊆ vertices ∧
        IsTwoThirdsBalancedVertexSeparator G vertices separator ∧
        separator.card = minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by sorry
