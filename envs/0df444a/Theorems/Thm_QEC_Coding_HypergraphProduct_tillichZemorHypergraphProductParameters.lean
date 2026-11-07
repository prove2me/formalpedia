-- Prove2me | Theorems.Thm_QEC_Coding_HypergraphProduct_tillichZemorHypergraphProductParameters
-- name    : QEC.Coding.HypergraphProduct.tillichZemorHypergraphProductParameters
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:42:46.736203+00:00
-- url     : https://prove2.me/theorems/319459ca-031a-483b-b5bd-56ca85714b60
-- title:
--   Hypergraph Product: tillich Zemor Hypergraph Product Parameters
-- statement:
--   The general two-input Tillich--Zémor hypergraph-product parameter theorem:
--   source validity, exact blocklength and dimension, the four-distance lower
--   bound and source equality cases, and the exact check/qubit degree formulas.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/HypergraphProductParameters.lean#L21-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/HypergraphProductParameters.lean#L21-L74

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Results_QLDPC_HypergraphProductParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u

theorem QEC.Coding.HypergraphProduct.tillichZemorHypergraphProductParameters
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    (binaryCSSCode D).stabilizer.IsSourceValidBinary ∧
    Fintype.card (QubitIndex rowOne colOne rowTwo colTwo) =
      Fintype.card colOne * Fintype.card colTwo +
        Fintype.card rowOne * Fintype.card rowTwo ∧
    Module.finrank (ZMod 2) (chainComplex D).middleHomology =
      Dimension (firstCode D) * Dimension (secondCode D) +
        Dimension (firstTransposeCode D) *
          Dimension (secondTransposeCode D) ∧
    inputDistanceMinimum D ≤
      extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode ∧
    (DistanceEqualityCondition D →
      extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode D).xCode (binaryCSSCode D).zCode =
        inputDistanceMinimum D) ∧
    (∀ r₁ c₂, HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (r₁, c₂) 1)) =
      rowWeight D.first r₁ + columnWeight D.second c₂) ∧
    (∀ c₁ r₂, HammingWeight (boundary2 D (Pi.single (c₁, r₂) 1)) =
      rowWeight D.second r₂ + columnWeight D.first c₁) ∧
    (∀ c₁ c₂, qubitDegree D (Sum.inl (c₁, c₂)) =
      columnWeight D.first c₁ + columnWeight D.second c₂) ∧
    (∀ r₁ r₂, qubitDegree D (Sum.inr (r₁, r₂)) =
      rowWeight D.second r₂ + rowWeight D.first r₁) ∧
    (∀ w,
      (∀ r, rowWeight D.first r ≤ w) →
      (∀ c, columnWeight D.first c ≤ w) →
      (∀ r, rowWeight D.second r ≤ w) →
      (∀ c, columnWeight D.second c ≤ w) →
      ((∀ x₀, HammingWeight
          (wordLinearMapTranspose (boundary1 D) (Pi.single x₀ 1)) ≤ 2 * w) ∧
       (∀ x₂, HammingWeight (boundary2 D (Pi.single x₂ 1)) ≤ 2 * w) ∧
       (∀ q, qubitDegree D q ≤ 2 * w))) := by sorry
