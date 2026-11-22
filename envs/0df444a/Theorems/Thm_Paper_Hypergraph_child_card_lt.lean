-- Prove2me | Theorems.Thm_Paper_Hypergraph_child_card_lt
-- name    : Paper.Hypergraph.child_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:11.449904+00:00
-- url     : https://prove2.me/theorems/851a0c4e-740c-4676-8e7b-eaa31667554a
-- title:
--   Hypergraph: child card lt
-- statement:
--   Removing the pivot makes every recursive call strictly smaller.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1744-L1756
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/Formalized.lean#L1744-L1756

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph

theorem Paper.Hypergraph.child_card_lt (H : Hypergraph) {W Z B K : Finset ℕ} {u : ℕ}
    (hZB : Z ⊆ B) (hu : u ∈ W \ Z) (huB : u ∈ B)
    (hK : K ∈ (H.induce (W \ B)).components) : K.card < (W \ Z).card := by sorry
