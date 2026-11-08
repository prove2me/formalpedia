-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_tillichZemorHypergraphProductDiagonalFullRank
-- name    : QEC.Coding.HypergraphProduct.tillichZemorHypergraphProductDiagonalFullRank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:42:55.042585+00:00
-- url     : https://prove2.me/theorems/efc8e2e4-6dca-442e-9af2-82dabf282a92
-- title:
--   Hypergraph Product: tillich Zemor Hypergraph Product Diagonal Full Rank
-- statement:
--   The diagonal full-rank specialization stated in the introduction of TZ09.
--   Here `n = card Col`, `k = Dimension (ker H)`, the blocklength is
--   `n² + (n-k)²`, the encoded dimension is `k²`, the quantum distance is
--   the classical distance, and every displayed stabilizer row has weight equal
--   to an input row weight plus an input column weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/HypergraphProductParameters.lean#L81-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/HypergraphProductParameters.lean#L81-L106

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Results_QLDPC_HypergraphProductParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u

theorem QEC.Coding.HypergraphProduct.tillichZemorHypergraphProductDiagonalFullRank
    {Row Col : Type u}
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (H : Matrix Row Col (ZMod 2))
    (hFull : Function.Surjective (Matrix.toLin' H)) :
    Fintype.card (QubitIndex Row Col Row Col) =
      Fintype.card Col ^ 2 +
        (Fintype.card Col - Dimension (firstCode (diagonalData H))) ^ 2 ∧
    Module.finrank (ZMod 2) (chainComplex (diagonalData H)).middleHomology =
      Dimension (firstCode (diagonalData H)) ^ 2 ∧
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode (diagonalData H)).xCode
        (binaryCSSCode (diagonalData H)).zCode =
      extendedMinimumDistance (firstCode (diagonalData H)) ∧
    (∀ r c, HammingWeight
        (wordLinearMapTranspose (boundary1 (diagonalData H))
          (Pi.single (r, c) 1)) =
      rowWeight H r + columnWeight H c) ∧
    (∀ c r, HammingWeight
        (boundary2 (diagonalData H) (Pi.single (c, r) 1)) =
      rowWeight H r + columnWeight H c) := by sorry
