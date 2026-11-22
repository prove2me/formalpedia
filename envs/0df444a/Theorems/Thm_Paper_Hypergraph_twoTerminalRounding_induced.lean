-- Prove2me | Theorems.Thm_Paper_Hypergraph_twoTerminalRounding_induced
-- name    : Paper.Hypergraph.twoTerminalRounding_induced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:34.114973+00:00
-- url     : https://prove2.me/theorems/28c36928-a20a-4bb9-916f-f4096c629266
-- title:
--   Hypergraph: two Terminal Rounding induced
-- statement:
--   Apply two-terminal rounding in an induced hypergraph while charging costs
--   and structural factors to the original hypergraph.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L55-L74
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/TwoTerminalRounding.lean#L55-L74

import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_TwoTerminalRounding
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.twoTerminalRounding_induced (round : TwoTerminalRounding) (H : Hypergraph)
    (Q : Finset ℕ) (x : ℕ → ℝ) (A B : Finset ℕ) (z : ℕ → ℝ)
    (hA : A ⊆ (H.induce Q).vertices) (hB : B ⊆ (H.induce Q).vertices)
    (hz : (H.induce Q).FractionalSeparator A B z)
    (hsupp : ∀ v ∈ (H.induce Q).vertices, z v ≠ 0 → x v ≠ 0) :
    ∃ S ⊆ (H.induce Q).vertices.filter (fun v => z v ≠ 0),
      (H.induce Q).IntegralSeparator A B S ∧
      H.setCoverCost S ≤ H.twoTerminalFactor (H.vertices.filter (fun v => x v ≠ 0)) *
        (H.induce Q).coverCost z := by sorry
