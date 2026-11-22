-- Prove2me | Theorems.Thm_Paper_Hypergraph_separatorRegion_disjoint_terminals
-- name    : Paper.Hypergraph.separatorRegion_disjoint_terminals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:55.447888+00:00
-- url     : https://prove2.me/theorems/41244ded-dd4f-44c8-8d5e-e631f642ec82
-- title:
--   Hypergraph: separator Region disjoint terminals
-- statement:
--   The Hypergraph construction uses the separator Region disjoint terminals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L28-L33
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingSeparation.lean#L28-L33

import Definitions.Def_Paper_RoundingPaths
import Definitions.Def_Paper_RoundingSeparation
set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.separatorRegion_disjoint_terminals (H : Hypergraph) {A B S : Finset ℕ}
    (hsep : H.IntegralSeparator A B S) : Disjoint (H.separatorRegion A S) B := by sorry
