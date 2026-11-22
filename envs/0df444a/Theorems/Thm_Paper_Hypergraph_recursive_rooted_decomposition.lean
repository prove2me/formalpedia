-- Prove2me | Theorems.Thm_Paper_Hypergraph_recursive_rooted_decomposition
-- name    : Paper.Hypergraph.recursive_rooted_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:20.701798+00:00
-- url     : https://prove2.me/theorems/fd349666-731f-422c-bade-68f797882e41
-- title:
--   Hypergraph: recursive rooted decomposition
-- statement:
--   The rooted invariant used in the LaTeX separator recursion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1888-L2009
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1888-L2009

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.recursive_rooted_decomposition (H : Hypergraph) {η r : ℝ}
    (hη : 0 < η ∧ η < 1) (hr : H.sep η < r)
    (W Z : Finset ℕ) (hW : W ⊆ H.vertices) (hZ : Z ⊆ W)
    (hcost : H.setCoverCost Z ≤ (r + 1) / (1 - η)) :
    ∃ n, ∃ D : (H.induce W).TreeDecomposition n, ∃ root, Z ⊆ D.bag root ∧
      ∀ t, H.setCoverCost (D.bag t) ≤ (r + 1) / (1 - η) + r + 1 := by sorry
