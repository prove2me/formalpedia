-- Prove2me | Theorems.Thm_QEC_Locality_UnitSeparatedEmbedding2D_distance_nonneg
-- name    : QEC.Locality.UnitSeparatedEmbedding2D.distance_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:33:32.976261+00:00
-- url     : https://prove2.me/theorems/9c6d70f6-4103-4369-98cd-ed23b8bbc07e
-- title:
--   Unit Separated Embedding2 D: distance nonneg
-- statement:
--   Distance is nonnegative for every pair of embedded qubits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L66-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/Interaction.lean#L66-L68

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

theorem QEC.Locality.UnitSeparatedEmbedding2D.distance_nonneg (embedding : UnitSeparatedEmbedding2D ι) (p q : ι) :
    0 ≤ embedding.distance p q := by sorry
