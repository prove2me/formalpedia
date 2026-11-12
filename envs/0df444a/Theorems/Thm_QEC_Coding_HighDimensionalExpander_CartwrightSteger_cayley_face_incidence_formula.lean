-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cayley_face_incidence_formula
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cayley_face_incidence_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:40:39.023404+00:00
-- url     : https://prove2.me/theorems/31ecc861-7564-4c70-b5af-0fcea48b6dbf
-- title:
--   Cartwright Steger: cayley face incidence formula
-- statement:
--   Exact face-incidence formula for a finite Cayley clique complex.  The
--   rightmost factor is computed at the identity, and left translation proves
--   that the same number of faces is incident to every vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1401-L1442
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1401-L1442

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
variable {Γ : Type u} [Group Γ] [Fintype Γ] [DecidableEq Γ]

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cayley_face_incidence_formula
    (S : Set Γ) (p : Nat) :
    p * Fintype.card
        (SimplicialChain.Face (CayleyClique.cayleyCliqueComplex S) p) =
      Fintype.card Γ *
        Fintype.card
          {σ : SimplicialChain.Face
              (CayleyClique.cayleyCliqueComplex S) p //
            1 ∈ σ.vertices} := by sorry
