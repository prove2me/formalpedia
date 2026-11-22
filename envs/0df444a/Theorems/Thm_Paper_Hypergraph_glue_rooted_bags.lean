-- Prove2me | Theorems.Thm_Paper_Hypergraph_glue_rooted_bags
-- name    : Paper.Hypergraph.glue_rooted_bags
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:20.338783+00:00
-- url     : https://prove2.me/theorems/2a638e59-71f7-42fc-838d-feac136a5996
-- title:
--   Hypergraph: glue rooted bags
-- statement:
--   Rooted gluing preserves running intersection when shared vertices occur in the roots.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1840-L1885
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1840-L1885

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.glue_rooted_bags (H : Hypergraph) {I : Type*} [Fintype I]
    {V : I → Type*} [∀ i, Fintype (V i)]
    (G : ∀ i, SimpleGraph (V i)) (hG : ∀ i, (G i).IsTree)
    (bag : ∀ i, V i → Finset ℕ) (root : ∀ i, V i) (o : I)
    (hsub : ∀ i t, bag i t ⊆ H.vertices)
    (hedge : ∀ e ∈ H.edges, ∃ i t, H.edge e ⊆ bag i t)
    (hvertex : ∀ v ∈ H.vertices, ∃ i t, v ∈ bag i t)
    (hrun : ∀ i v, (G i |>.induce {t | v ∈ bag i t}).Preconnected)
    (hlocal : ∀ i t, bag i t ∩ bag o (root o) ⊆ bag i (root i))
    (hoverlap : ∀ i j, i ≠ j → ∀ a c, bag i a ∩ bag j c ⊆ bag o (root o))
    (b : Finset ℕ → ℝ) (r : ℝ) (hwidth : ∀ i t, b (bag i t) ≤ r) :
    ∃ n, ∃ D : H.TreeDecomposition n, ∃ t, bag o (root o) ⊆ D.bag t ∧
      ∀ t, b (D.bag t) ≤ r := by sorry
