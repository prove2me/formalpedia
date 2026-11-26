-- Prove2me | Theorems.Thm_TDLC_betaEtaLoopNontrivial
-- name    : TDLC.betaEtaLoopNontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:23.137388+00:00
-- url     : https://prove2.me/theorems/196d95ff-2715-5d53-ad3a-f5372a50800e
-- title:
--   TDLC: beta Eta Loop Nontrivial
-- statement:
--   The beta/eta loop is not connected by any two-path to the empty path.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L835-L843
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L835-L843

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.betaEtaLoopNontrivial {A B : Type u} (f : A → B) (a : A) :
    Path2
      (Path.lEmbed (Step.beta f a) ++ₚ
        Path.inv (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))))
      (.nil (f a)) → False := by sorry
