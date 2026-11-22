-- Prove2me | Theorems.Thm_Paper_Hypergraph_main_width_comparison
-- name    : Paper.Hypergraph.main_width_comparison
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:21:13.860163+00:00
-- url     : https://prove2.me/theorems/4097a347-2fa3-4c81-a189-b8004e49e8da
-- title:
--   Hypergraph: main width comparison
-- statement:
--   The manuscript's main width comparison, with no external theorem hypothesis.
--
--   Source: https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingComplete.lean#L165-L166
-- source:
--   https://github.com/lnz/sparse-incidence-homomorphisms/blob/eaaead474600dd01474cf7d9504262daa49db386/Paper/RoundingComplete.lean#L165-L166

import Definitions.Def_Paper_RoundingIndependence
import Definitions.Def_Paper_RoundingDegeneracy
import Definitions.Def_Paper_BalancedRounding
import Definitions.Def_Paper_RoundingComplete
set_option autoImplicit true
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph

theorem Paper.Hypergraph.main_width_comparison : MainWidthComparison := by sorry
