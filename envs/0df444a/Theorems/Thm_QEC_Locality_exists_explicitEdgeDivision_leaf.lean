-- Prove2me | Theorems.Thm_QEC_Locality_exists_explicitEdgeDivision_leaf
-- name    : QEC.Locality.exists_explicitEdgeDivision_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:24:28.1342+00:00
-- url     : https://prove2.me/theorems/45f57103-1498-431b-bae6-fd551b10e8c7
-- title:
--   Locality: exists explicit Edge Division leaf
-- statement:
--   The canonical leaf data packaged existentially.  All witnesses are the explicit
--   definitions above; no division or cardinality conclusion is supplied as an
--   input hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L167-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/EdgeDivision.lean#L167-L182

import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
set_option autoImplicit false
open QEC QEC.Locality
universe u w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.exists_explicitEdgeDivision_leaf (G : ConnectivityGraph ι)
    {r : Nat} (hr : 2 ≤ r) :
    ∃ regions : (ι × ι) → Finset (ι × ι), ∃ active : Finset (ι × ι),
      IsEdgeDivision G regions active ∧
        (∀ owner, owner ∈ active →
          (edgeIncidentVertices (regions owner)).card ≤ r) ∧
        (∀ owner, owner ∈ active →
          ((edgeIncidentVertices (regions owner)) ∩
            edgeDivisionSharedBoundary regions active).card ≤ 2) ∧
        active.card ≤ (directedEdgeFinset G).card := by sorry
