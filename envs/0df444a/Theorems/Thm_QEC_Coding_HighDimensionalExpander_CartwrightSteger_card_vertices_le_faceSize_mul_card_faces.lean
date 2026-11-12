-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_vertices_le_faceSize_mul_card_faces
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_vertices_le_faceSize_mul_card_faces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:45:19.162449+00:00
-- url     : https://prove2.me/theorems/b1473ffc-a214-4958-8e68-94e65f791d12
-- title:
--   Cartwright Steger: card vertices le face Size mul card faces
-- statement:
--   If every vertex lies in a `p`-vertex face, double counting chosen vertex
--   incidences bounds the vertex count by `p` times the number of such faces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1267-L1286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1267-L1286

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
variable (K : AbstractSimplicialComplex V)
variable {K}

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_vertices_le_faceSize_mul_card_faces
    (p : Nat)
    (hcover : ∀ x : V, ∃ σ : SimplicialChain.Face K p,
      x ∈ σ.vertices) :
    Fintype.card V ≤
      p * Fintype.card (SimplicialChain.Face K p) := by sorry
