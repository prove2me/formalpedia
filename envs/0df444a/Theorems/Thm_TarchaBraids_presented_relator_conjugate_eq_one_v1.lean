-- Prove2me | Theorems.Thm_TarchaBraids_presented_relator_conjugate_eq_one_v1
-- name    : TarchaBraids.presented_relator_conjugate_eq_one_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T06:52:40.503323+00:00
-- url     : https://prove2.me/theorems/f8c4b33f-20b0-4dbe-9832-1b8321beba00
-- title:
--   A conjugate of an Artin relator is trivial in the presented braid group
-- statement:
--   The Artin braid presentation is the quotient of the free group by the normal closure of the commuting and adjacent braid relators. Consequently, after one elementary geometric move has been represented by a relator r, multiplying a current word on the left and right by the same context w and the inverse context w⁻¹ still gives the identity in the presented group. This child isolates the normal-closure/context algebra used when translating the geometric elementary-move analysis into the Artin presentation; it does not assert that every geometric null word is a relator.
-- source:
--   Tarcha, Um Estudo Introdutório da Teoria de Tranças, Theorem 3.15, pp. 59-62, elementary-move reduction; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem presented_relator_conjugate_eq_one_v1 (n : ℕ)
    (w r : FreeGroup (Fin (n - 1))) (hr : r ∈ braidRels n) :
    PresentedGroup.mk (braidRels n) (w * r * w⁻¹) = 1 := by sorry

end TarchaBraids
