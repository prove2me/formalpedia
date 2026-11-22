-- Prove2me | Theorems.Thm_Paper_Hypergraph_support_integralSeparator
-- name    : Paper.Hypergraph.support_integralSeparator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:10.355146+00:00
-- url     : https://prove2.me/theorems/723d287e-00d4-4476-bd7e-852bffb4c49d
-- title:
--   Hypergraph: support integral Separator
-- statement:
--   Fractional separation forces integral separation after zero-demand vertices
--   are retained. This also discharges the empty-support branch of rounding.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L59-L81
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L59-L81

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.support_integralSeparator (H : Hypergraph) {A B : Finset ℕ} {x : ℕ → ℝ}
    (hA : A ⊆ H.vertices) (hx : H.FractionalSeparator A B x) :
    H.IntegralSeparator A B (H.vertices.filter fun v => x v ≠ 0) := by sorry
