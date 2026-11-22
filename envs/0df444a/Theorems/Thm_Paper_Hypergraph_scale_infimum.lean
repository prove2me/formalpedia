-- Prove2me | Theorems.Thm_Paper_Hypergraph_scale_infimum
-- name    : Paper.Hypergraph.scale_infimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:14.425533+00:00
-- url     : https://prove2.me/theorems/6b5c697f-81a8-4aca-b743-1fe330ed73f0
-- title:
--   Hypergraph: scale infimum
-- statement:
--   Pass to the optimum by continuity; attainment is not required.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2494-L2505
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L2494-L2505

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.scale_infimum {A : Set ℝ} (hne : A.Nonempty) (hA : ∀ r ∈ A, 0 ≤ r)
    {c : ℝ} (hc : 0 ≤ c) :
    c * (sInf A + 1) * Real.log (2 + sInf A) =
      sInf ((fun r => c * (r + 1) * Real.log (2 + r)) '' A) := by sorry
