-- Prove2me | Theorems.Thm_QEC_Locality_edgeIncidentVertices_mono
-- name    : QEC.Locality.edgeIncidentVertices_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:27.45047+00:00
-- url     : https://prove2.me/theorems/5b3937db-0300-4f09-84d8-ccee2f370cd0
-- title:
--   Locality: edge Incident Vertices mono
-- statement:
--   Incident-vertex sets are monotone under edge-set inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L397-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L397-L402

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.edgeIncidentVertices_mono {edges₁ edges₂ : Finset (ι × ι)}
    (hsubset : edges₁ ⊆ edges₂) :
    edgeIncidentVertices edges₁ ⊆ edgeIncidentVertices edges₂ := by sorry
