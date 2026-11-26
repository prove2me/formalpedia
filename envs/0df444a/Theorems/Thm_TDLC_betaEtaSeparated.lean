-- Prove2me | Theorems.Thm_TDLC_betaEtaSeparated
-- name    : TDLC.betaEtaSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:25:20.326299+00:00
-- url     : https://prove2.me/theorems/4d7ebe21-cfe5-5c74-9339-937dc5831a53
-- title:
--   TDLC: beta Eta Separated
-- statement:
--   The beta-labelled and eta-labelled routes with the same endpoints cannot be joined.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L825-L832
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L825-L832

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.betaEtaSeparated {A B : Type u} (f : A → B) (a : A) :
    Step2
      (Path.lEmbed (Step.beta f a))
      (Path.lEmbed (Step.apCong (fun k : A → B => k a) (Step.eta f))) → False := by sorry
