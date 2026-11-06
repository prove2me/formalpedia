-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_one_le_distance_of_ne
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.one_le_distance_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:50:10.448926+00:00
-- url     : https://prove2.me/theorems/32b83a69-3a5f-4b4d-a089-0ce141d369a4
-- title:
--   Unit Separated Embedding2 D: one le distance of ne
-- statement:
--   The stored unit-separation condition exposes the source convention directly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L60-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L60-L63

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC
open QEC.Locality
open QEC.Locality.UnitSeparatedEmbedding2D
variable {ι : Type*}

theorem QEC.Locality.UnitSeparatedEmbedding2D.one_le_distance_of_ne (embedding : UnitSeparatedEmbedding2D ι)
    {p q : ι} (hpq : p ≠ q) :
    1 ≤ embedding.distance p q := by sorry
