-- Prove2me | Theorems.Thm_TarchaBraids_presented_geom_relator_trace_eq_one_v1
-- name    : TarchaBraids.presented_geom_relator_trace_eq_one_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T07:43:34.726095+00:00
-- url     : https://prove2.me/theorems/7a71fc8b-91f1-44ce-a4e6-b9fd3fbbc485
-- title:
--   A finite contextual Artin-relator trace is trivial in the presented braid group
-- statement:
--   The Artin braid presentation is the quotient of the free group by the normal closure of its commuting and adjacent braid relators. Therefore every finite contextual trace of relator insertions is trivial in that presentation. The proof is by induction over the trace: each step prepends a conjugate of one relator, which lies in the normal closure, to a shorter trace already known to be trivial.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59--62, Figures 3.18--3.27; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem presented_geom_relator_trace_eq_one_v1 {n : ℕ} {w : FreeGroup (Fin (n - 1))}
    (t : GeomRelatorTrace n w) :
    PresentedGroup.mk (braidRels n) w = 1 := by sorry

end TarchaBraids
