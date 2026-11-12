-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_cofaces_le_extensionVertices
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_cofaces_le_extensionVertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:59:05.001026+00:00
-- url     : https://prove2.me/theorems/7292fe83-17a2-426d-b4f9-c259c3615f89
-- title:
--   Cartwright Steger: card cofaces le extension Vertices
-- statement:
--   Codimension-one cofaces inject into the vertices which extend a face.
--   This bridge derives the coface count from the actual simplicial complex; it
--   does not accept a locality table as data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1556-L1580
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1556-L1580

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {K : AbstractSimplicialComplex V} {p : Nat}

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_cofaces_le_extensionVertices
    (σ : SimplicialChain.Face K p) :
    (SimplicialChain.cofaces K p σ).card ≤
      (CayleyClique.extensionVertices K σ.vertices).card := by sorry
