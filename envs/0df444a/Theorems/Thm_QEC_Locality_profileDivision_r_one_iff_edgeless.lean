-- Prove2me | Theorems.Thm_QEC_Locality_profileDivision_r_one_iff_edgeless
-- name    : QEC.Locality.profileDivision_r_one_iff_edgeless
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:01:27.981+00:00
-- url     : https://prove2.me/theorems/d0f992a4-213b-43b3-85d9-b9634d5fe504
-- title:
--   Locality: profile Division r one iff edgeless
-- statement:
--   The only `r = 1` completion is the edgeless branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/ExplicitDivision.lean#L235-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/ExplicitDivision.lean#L235-L248

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.profileDivision_r_one_iff_edgeless
    (G : ConnectivityGraph ι) :
    (∃ (m : Type) (_ : DecidableEq m) (regions : m → Finset (ι × ι))
      (active : Finset m), IsEdgeDivision G regions active ∧
        ∀ owner, owner ∈ active → (edgeIncidentVertices (regions owner)).card ≤ 1) ↔
      directedEdgeFinset G = ∅ := by sorry
