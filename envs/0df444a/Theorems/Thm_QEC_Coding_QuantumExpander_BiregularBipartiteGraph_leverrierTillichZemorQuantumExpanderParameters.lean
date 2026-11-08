-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_leverrierTillichZemorQuantumExpanderParameters
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.leverrierTillichZemorQuantumExpanderParameters
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:43:09.882971+00:00
-- url     : https://prove2.me/theorems/84764176-08fc-46a0-953a-86d31557acf6
-- title:
--   Biregular Bipartite Graph: leverrier Tillich Zemor Quantum Expander Parameters
-- statement:
--   Exact finite Leverrier--Tillich--Zemor quantum-expander construction and
--   distance theorem.  The graph supplies its incidence matrix internally; every
--   parameter and distance conclusion is derived.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/QuantumExpanderParameters.lean#L27-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/QLDPC/QuantumExpanderParameters.lean#L27-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
import Definitions.Def_QEC_Results_QLDPC_QuantumExpanderParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.leverrierTillichZemorQuantumExpanderParameters
    (G : QEC.Coding.QuantumExpander.BiregularBipartiteGraph A B)
    (hSize : Fintype.card B ≤ Fintype.card A)
    {γA δA γB δB : Real}
    (hγA : 0 < γA) (hδApos : 0 < δA)
    (hγB : 0 < γB) (hδBpos : 0 < δB)
    (hExpand : G.LeftRightExpanding γA δA γB δB)
    (hδA : δA < 1 / 2) (hδB : δB < 1 / 2) :
    G.leftDegree ≤ G.rightDegree ∧
    (binaryCSSCode G.hypergraphProductData).stabilizer.IsSourceValidBinary ∧
    Fintype.card (QubitIndex B A B A) =
      Fintype.card A ^ 2 + Fintype.card B ^ 2 ∧
    (Fintype.card A - Fintype.card B) ^ 2 ≤
      Module.finrank (ZMod 2)
        (chainComplex G.hypergraphProductData).middleHomology ∧
    (∀ b a, HammingWeight
        (wordLinearMapTranspose (boundary1 G.hypergraphProductData)
          (Pi.single (b, a) 1)) = G.leftDegree + G.rightDegree) ∧
    (∀ a b, HammingWeight
        (boundary2 G.hypergraphProductData (Pi.single (a, b) 1)) =
          G.leftDegree + G.rightDegree) ∧
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode G.hypergraphProductData).xCode
        (binaryCSSCode G.hypergraphProductData).zCode =
      min
        (extendedMinimumDistance (firstCode G.hypergraphProductData))
        (extendedMinimumDistance
          (firstTransposeCode G.hypergraphProductData)) ∧
    ENNReal.ofReal
        (min (γA * Fintype.card A) (γB * Fintype.card B)) ≤
      extendedNatToENNReal
        (extendedAlgebraicCSSMinimumDistance
          (binaryCSSCode G.hypergraphProductData).xCode
          (binaryCSSCode G.hypergraphProductData).zCode) := by sorry
