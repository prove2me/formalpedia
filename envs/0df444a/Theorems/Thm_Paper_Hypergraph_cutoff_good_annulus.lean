-- Prove2me | Theorems.Thm_Paper_Hypergraph_cutoff_good_annulus
-- name    : Paper.Hypergraph.cutoff_good_annulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:24.8354+00:00
-- url     : https://prove2.me/theorems/561036d4-643a-4152-aa6d-6754770afe17
-- title:
--   Hypergraph: cutoff good annulus
-- statement:
--   The repaired layer argument, now instantiated with actual hypergraph balls.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean#L12-L67
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingCutoff.lean#L12-L67

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
import Definitions.Def_Paper_RoundingCutoff
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.cutoff_good_annulus (H : Hypergraph) {x : ℕ → ℝ}
    (hx : ∀ v ∈ H.vertices, 0 ≤ x v) (Q : Finset ℕ) {c : ℕ}
    (hc : c ∈ H.vertices ∩ Q) {r q : ℝ} (hr : 0 < r)
    (hK : r / 2 ≤ H.coverCost x)
    (hq0 : 0 ≤ q) (hq : ∀ v ∈ H.vertices ∩ Q, x v ≤ q)
    (hsmall : q < (r / (9 + 2 * Real.logb 2 (H.coverCost x / r))) / 2)
    (hout : ∃ v, (H.induce Q).primal.Reachable c v ∧
      r / 4 < (H.induce Q).vertexDistance x c v) :
    let δ := r / (9 + 2 * Real.logb 2 (H.coverCost x / r))
    ∃ s : ℝ, r / 4 ≤ s ∧ s + 3 * δ / 2 ≤ r ∧
      H.coverCost (restrictDemand x
        (H.roundingBall x Q c (s + 3 * δ / 2) \ H.roundingBall x Q c (s + δ / 2))) ≤
        H.coverCost (restrictDemand x (H.roundingBall x Q c s)) := by sorry
